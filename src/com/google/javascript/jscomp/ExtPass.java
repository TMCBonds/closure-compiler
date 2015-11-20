// Written by Daniel Kasierer
// for TMC Bonds

package com.google.javascript.jscomp;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;
import com.google.javascript.jscomp.NodeTraversal.AbstractPostOrderCallback;
import com.google.javascript.jscomp.parsing.JsDocInfoParser;
import com.google.javascript.rhino.IR;
import com.google.javascript.rhino.JSDocInfo;
import com.google.javascript.rhino.JSDocInfoBuilder;
import com.google.javascript.rhino.JSTypeExpression;
import com.google.javascript.rhino.Node;
import com.google.javascript.rhino.Token;
import java.util.logging.Logger;
import java.util.Properties;
import java.io.FileReader;
import java.io.File;
import java.util.List;

class ExtPass extends AbstractPostOrderCallback
    implements CompilerPass {
  final AbstractCompiler compiler;
  private static final Logger logger =
      Logger.getLogger(ExtPass.class.getName());
  private static String EXT;
  private final List<Node> defineCalls = Lists.newArrayList();
  private final List<Node> anonymousDefineCalls = Lists.newArrayList();
  private final List<Node> createCalls = Lists.newArrayList();
  private final List<Node> extendDefs = Lists.newArrayList();
  static final DiagnosticType INVALID_CLOSURE_CALL_ERROR = DiagnosticType.error(
      "JSC_INVALID_CLOSURE_CALL_ERROR",
      "Closure dependency methods(Ext6.define, Ext6.extends, etc) must be called at file scope.");
  static final DiagnosticType INVALID_DEFINE_NAME_ERROR = DiagnosticType.error(
      "JSC_INVALID_DEFINE_NAME_ERROR",
      "\"{0}\" is not a valid JS identifier name");
  static final DiagnosticType MISSING_DEFINE_ANNOTATION = DiagnosticType.error(
      "JSC_INVALID_MISSING_DEFINE_ANNOTATION",
      "Missing @define annotation");
  static final DiagnosticType NULL_ARGUMENT_ERROR = DiagnosticType.error(
      "JSC_NULL_ARGUMENT_ERROR",
      "method \"{0}\" called without an argument");
  static final DiagnosticType INVALID_ARGUMENT_ERROR = DiagnosticType.error(
      "JSC_INVALID_ARGUMENT_ERROR",
      "method \"{0}\" called with invalid argument");

  public ExtPass(AbstractCompiler compiler) {
    this.compiler = compiler;
    try {
      Properties prop = new Properties();
      prop.load(this.getClass().getResourceAsStream("ExtConfig.properties"));
      EXT = prop.getProperty("ext_base", "Ext");
    }
    catch(Exception e) {
      EXT = "Ext";
    }
  }

  @Override
  public void process(Node externs, Node root) {
    logger.fine("Adding Extjs annotations");
    new NodeTraversal(compiler, this).traverse(root);

    for (Node n : extendDefs) {
      annotateExtends(n);
    }

    for (Node n : defineCalls) {
      replaceExtDefines(n);
    }

    for (Node n : anonymousDefineCalls) {
      replaceExtAnonymousDefines(n);
    }

    for (Node n : createCalls) {
      replaceExtCreates(n);
    }
  }

  @Override
  public void visit(NodeTraversal t, Node n, Node parent) {
    if(Token.CALL == n.getType()) {
      Node left = n.getFirstChild();
      if (left.isGetProp()) {
        Node name = left.getFirstChild();
        if (name.isName() &&
            EXT.equals(name.getString())) {
          String methodName = name.getNext().getString();
          if ("define".equals(methodName)) {
            Node className = left.getNext();
            if (className.getType() == Token.NULL) {
              processAnonymousDefineCall(t, n, parent);
            }
            else {
              processDefineCall(t, n, parent);
            }
          }
          else if("create".equals(methodName)) {
            processCreateCall(t, n, parent);
          }
        }
      }
    }
    else if(Token.STRING_KEY == n.getType()) {
      if("extend".equals(n.getString())) {
        processExtend(t, n, parent);
      }
    }
  }

  private void processDefineCall(NodeTraversal t, Node n, Node parent) {
    Node left = n.getFirstChild();
    Node args = left.getNext();
    if (verifyDefine(t, parent, left, args)) {
      Node nameNode = args;
      this.defineCalls.add(n);
    }
  }

  private void processAnonymousDefineCall(NodeTraversal t, Node n, Node parent) {
    Node left = n.getFirstChild();
    Node args = left.getNext();
    if (verifyAnonymousDefine(t, parent, left, args)) {
      Node nameNode = args;
      this.anonymousDefineCalls.add(n);
    }
  }

  private void processCreateCall(NodeTraversal t, Node n, Node parent) {
    Node left = n.getFirstChild();
    Node args = left.getNext();
    if (verifyCreate(t, parent, left, args)) {
      Node nameNode = args;
      this.createCalls.add(n);
    }
  }

  private void processExtend(NodeTraversal t, Node n, Node parent) {
    if(verifyExtend(t, n, parent)) {
      this.extendDefs.add(n);
    }
  }
  private boolean verifyDefine(NodeTraversal t,
      Node expr,
      Node methodName, Node args) {
    // Verify first arg
    Node arg = args;
    if (!verifyNotNull(t, methodName, arg) ||
        !verifyOfType(t, methodName, arg, Token.STRING)) {
      return false;
    }

    // Verify second arg
    arg = arg.getNext();
    if (!verifyNotNull(t, methodName, arg) ||
        !verifyOfType(t, methodName, arg, Token.OBJECTLIT)) {
      return false;
    }

    String name = args.getString();
    if (!NodeUtil.isValidQualifiedName(compiler.getLanguageMode(), name)) {
      compiler.report(t.makeError(args, INVALID_DEFINE_NAME_ERROR, name));
      return false;
    }

    return true;
  }

  private boolean verifyCreate(NodeTraversal t,
      Node expr,
      Node methodName, Node args) {

    Node arg = args;

    if(!verifyNotNull(t, methodName, arg) ||
       !(NodeUtil.getKnownValueType(arg) == NodeUtil.ValueType.STRING)) {
      JSDocInfo info = expr.getJSDocInfo();
      if(info == null || !info.isTmcSuppress()) {
        Node parent = expr.getParent();
        if(parent != null) {
          JSDocInfo parentInfo = parent.getJSDocInfo();
          if(parentInfo == null || !parentInfo.isTmcSuppress()) {
            System.out.println("WARNING: Usage of Ext.create is not standard: " + arg.toString());
          }
        }
        else {
          System.out.println("WARNING: Usage of Ext.create is not standard: " + arg.toString());
        }
      }
      return false;
    }
    return true;
  }

  private boolean verifyAnonymousDefine(NodeTraversal t,
      Node expr,
      Node methodName, Node args) {
    Node self = methodName.getParent();
    if (!verifyNotNull(t, methodName, self) ||
        !verifyOfType(t, methodName, self, Token.CALL)) {
      return false;
    }

    // Verify first arg
    Node arg = args;
    if (!verifyNotNull(t, methodName, arg) ||
        !verifyOfType(t, methodName, arg, Token.NULL)) {
      return false;
    }

    // Verify second arg
    arg = arg.getNext();
    if (!verifyNotNull(t, methodName, arg) ||
        !verifyOfType(t, methodName, arg, Token.OBJECTLIT)) {
      return false;
    }

    return true;
  }

  private boolean verifyExtend(NodeTraversal t, Node n, Node parent) {
    // child should be string
    Node child = n.getFirstChild();
    if (child.getType() != Token.STRING) {
      return false;
    }
    // parent should be OBJECTLIT
    if(parent.getType() != Token.OBJECTLIT) {
      return false;
    }
    // grandParent should be ASSIGN
    Node grandParent = parent.getParent();
    if(grandParent == null || grandParent.getType() != Token.CALL) {
      return false;
    }
    Node left = grandParent.getFirstChild();
    if (left.isGetProp()) {
      Node name = left.getFirstChild();
      if (name.isName() &&
          EXT.equals(name.getString())) {
        String methodName = name.getNext().getString();
        if ("define".equals(methodName)) {
          Node className = left.getNext();
          if (className.getType() == Token.NULL) {
            return verifyAnonymousDefine(t, grandParent.getParent(), left, left.getNext());
          }
          else {
            return verifyDefine(t, grandParent.getParent(), left, left.getNext());
          }
        }
      }
    }
    return false;
  }
  private void replaceExtDefines(Node n) {
    //parent is the EXPR_RESULT level. parent.getParent() is script level
    Node parent = n.getParent();
    //name is the full namespaced name eg com.example.ClassName
    String name = n.getChildAtIndex(1).getString();
    //value is the object literal for the new class
    Node value = n.getChildAtIndex(2).detachFromParent();
    //constructor is the constructor definition eg. something = function(){};
    Node constructor = IR.function(
        IR.name("").srcref(n),
        IR.paramList(IR.name("config")).srcref(n),
        IR.block().srcref(n));
    constructor.srcref(n);

    JSDocInfoBuilder infoBuilder = JSDocInfoBuilder.maybeCopyFrom(n.getJSDocInfo());
    infoBuilder.recordConstructor();
    infoBuilder.recordParameter("config", new JSTypeExpression(new Node(Token.EQUALS, IR.string("Object")), ""));
    JSDocInfo info = infoBuilder.build();


    Node replacement = NodeUtil.newQNameDeclaration(
        compiler, name, constructor, info);
    replacement.useSourceInfoIfMissingFromForTree(n);
    parent.getParent().replaceChild(parent, replacement);

    Node replacement2 = NodeUtil.newQNameDeclaration(
        compiler, name + ".prototype", value, n.getJSDocInfo());
    replacement2.useSourceInfoIfMissingFromForTree(n);
    replacement.getParent().addChildAfter(replacement2, replacement);
    compiler.reportCodeChange();
  }

  private void replaceExtAnonymousDefines(Node n) {
    //
    //
    // Goal:
    //    convert:
    //        Ext.define(null, {...})
    //    to:
    //       (function(){ var a1 = function(){}; a1.prototype = {...}; return new a1(); })()
    //
    /* block for correct output
        VAR 78 [source_file: build/testfile.js]
            NAME a 78 [source_file: build/testfile.js]
                CALL 78 [free_call: 1] [source_file: build/testfile.js]
                    FUNCTION  78 [source_file: build/testfile.js]
                        NAME  78 [source_file: build/testfile.js]
                        PARAM_LIST 78 [source_file: build/testfile.js]
                        BLOCK 78 [source_file: build/testfile.js]
                            VAR 82 [jsdoc_info: JSDocInfo] [source_file: build/testfile.js]##VAR###docInfo: JSDocInfo{bitset=2, visibility=INHERITED}#####
                                NAME a1 82 [source_file: build/testfile.js]
                                    FUNCTION  82 [source_file: build/testfile.js]
                                        NAME  82 [source_file: build/testfile.js]
                                        PARAM_LIST 82 [source_file: build/testfile.js]
                                        BLOCK 82 [source_file: build/testfile.js]
                            EXPR_RESULT 83 [source_file: build/testfile.js]
                                ASSIGN 83 [source_file: build/testfile.js]
                                    GETPROP 83 [source_file: build/testfile.js]
                                        NAME a1 83 [source_file: build/testfile.js]
                                        STRING prototype 83 [source_file: build/testfile.js]
                                    OBJECTLIT 83 [source_file: build/testfile.js]
                            RETURN 84 [source_file: build/testfile.js]
                                NAME a1 84 [source_file: build/testfile.js] */
    //parent is the ASSIGN/NAME level. parent.getParent is EXPR_RESULT/VAR
    Node parent = n.getParent();
    // n is the CALL node
    // This define is anonymous so name is null
    //value is the object literal for the new class
    Node value = n.getChildAtIndex(2).detachFromParent();
    //constructor is the constructor definition eg. something = function(){};
    Node constructor = IR.function(
        IR.name("").srcref(n),
        IR.paramList().srcref(n),
        IR.block().srcref(n));
    constructor.srcref(n);
    String tmpClassName = "dummyName";
    Node name = IR.name(tmpClassName);
    JSDocInfoBuilder infoBuilder = null;
    if(parent.getType() == Token.ASSIGN) {
      infoBuilder = JSDocInfoBuilder.maybeCopyFrom(parent.getJSDocInfo());
    }
    else if (parent.getType() == Token.NAME) {// this is VAR
      Node variable = parent.getParent();
      infoBuilder = JSDocInfoBuilder.maybeCopyFrom(variable.getJSDocInfo());
    }
    else {
      // Likely CALL eg. Ext.create(Ext.define(null, {...}))
      infoBuilder = new JSDocInfoBuilder(true);
    }
    Node varNode = IR.var(name, constructor);
    infoBuilder.recordConstructor();
    JSDocInfo info = infoBuilder.build();
    varNode.setJSDocInfo(info);
    Node prototypeNode = NodeUtil.newQNameDeclaration(
        compiler, tmpClassName + ".prototype", value, n.getJSDocInfo());
    prototypeNode.useSourceInfoIfMissingFromForTree(n);
    Node returnNode = IR.returnNode(IR.name(tmpClassName));

    Node funcBlock = IR.block(varNode, prototypeNode, returnNode);
    Node callFunction = IR.function(
                          IR.name("").srcref(n),
                          IR.paramList().srcref(n),
                          funcBlock
                        );
    Node call = IR.call(callFunction);
    call.putBooleanProp(Node.FREE_CALL, true);

    parent.replaceChild(n, call);
    compiler.reportCodeChange();
  }

  private void replaceExtCreates(Node n) {
    Node nameNode = n.getChildAtIndex(1);
    String name = nameNode.getString();
    Node fqName = NodeUtil.newQName(compiler, name);
    nameNode.getParent().replaceChild(nameNode, fqName);
    compiler.reportCodeChange();
  }

  private void annotateExtends(Node n) {
    Node nameNode = n.getFirstChild();
    String name = nameNode.getString();
    Node constructor = n.getParent().getParent();

    JSDocInfoBuilder constructorDoc = JSDocInfoBuilder.maybeCopyFrom(constructor.getJSDocInfo());

    JSTypeExpression inherits = new JSTypeExpression(
                      new Node(Token.BANG, IR.string(name)), constructor.getSourceFileName());
    constructorDoc.recordBaseType(inherits);

    JSDocInfo info = constructorDoc.build();
    constructor.setJSDocInfo(info);
    compiler.reportCodeChange();
  }

  /**
   * @return Whether the argument checked out okay
   */
  private boolean verifyNotNull(NodeTraversal t, Node methodName, Node arg) {
    if (arg == null) {
      compiler.report(
          t.makeError(methodName,
              NULL_ARGUMENT_ERROR, methodName.getQualifiedName()));
      return false;
    }
    return true;
  }

  /**
   * @return Whether the argument checked out okay
   */
  private boolean verifyOfType(NodeTraversal t, Node methodName,
      Node arg, int desiredType) {
    if (arg.getType() != desiredType) {
      compiler.report(
          t.makeError(methodName,
              INVALID_ARGUMENT_ERROR, methodName.getQualifiedName()));
      return false;
    }
    return true;
  }
}

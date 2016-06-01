import java.io.FileInputStream;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.LinkedList;

import parser.*;
import parser.ast.*;
import parser.type.TypeInt;
import prism.ModelType;

public class PrismAnalyse {

  class StateMetric {
    String stateVar;
    int metric;

    public StateMetric(String stateVar, int metric) {
      this.stateVar = stateVar;
      this.metric = metric;
    }

    public int getMetric() {
      return metric;
    }

    public String getStateVar() {
      return stateVar;
    }

    public String toString() {
      return stateVar + ": " + metric;
    }
  }

  class StateMetricComparator implements Comparator<StateMetric> {

    boolean ascending;

    public StateMetricComparator(boolean ascending) {
      this.ascending = ascending;
    }

    public int compare(StateMetric g1, StateMetric g2) {
      if (g1.getMetric() < g2.getMetric()) {
        return ascending ? -1 : 1;
      } else if (g1.getMetric() > g2.getMetric()) {
        return ascending ? 1 : -1;
      } else {
        return 0;
      }
    }
  }

  ModulesFile mf;

  HashSet<String> stateVariables;
  HashSet<String> constantSet;
  HashSet<String> modules;
  HashMap<String, String> varModuleMap;
  HashMap<String, Expression> formulaExpressionMap;
  HashMap<String, ArrayList<String>> moduleVarListMap;
  HashMap<String, HashSet<String>> stateVarDependencies;
  HashMap<String, HashSet<String>> constantDependencies;

  void getExpressionStateVars(Expression e, HashSet<String> stateSet) {
    if (e instanceof ExpressionConstant) {
      return;
    } else if (e instanceof ExpressionLiteral) {
      return;
    } else if (e instanceof ExpressionBinaryOp) {
      ExpressionBinaryOp binOp = (ExpressionBinaryOp) e;
      getExpressionStateVars(binOp.getOperand1(), stateSet);
      getExpressionStateVars(binOp.getOperand2(), stateSet);
    } else if (e instanceof ExpressionUnaryOp) {
      ExpressionUnaryOp unaryOp = (ExpressionUnaryOp) e;
      getExpressionStateVars(unaryOp.getOperand(), stateSet);
    } else if (e instanceof ExpressionVar) {
      ExpressionVar eVar = (ExpressionVar) e;
      stateSet.add(eVar.getName());
    } else if (e instanceof ExpressionConstant) {
      return;
    } else if (e instanceof ExpressionFunc) {
      ExpressionFunc eFunc = (ExpressionFunc) e;
      for (int i = 0; i < eFunc.getNumOperands(); i++) {
        getExpressionStateVars(eFunc.getOperand(i), stateSet);
      }
    } else {
      System.out.println("WARNING: unsupported expression type found! " + e);
    }
  }

  void getExpressionConstants(Expression e, HashSet<String> stateSet) {
    if (e instanceof ExpressionConstant) {
      ExpressionConstant eConst = (ExpressionConstant) e;
      stateSet.add(eConst.getName());
    } else if (e instanceof ExpressionLiteral) {
      ExpressionLiteral eLit = (ExpressionLiteral) e;
      stateSet.add(eLit.toString());
    } else if (e instanceof ExpressionBinaryOp) {
      ExpressionBinaryOp binOp = (ExpressionBinaryOp) e;
      getExpressionConstants(binOp.getOperand1(), stateSet);
      getExpressionConstants(binOp.getOperand2(), stateSet);
    } else if (e instanceof ExpressionUnaryOp) {
      ExpressionUnaryOp unaryOp = (ExpressionUnaryOp) e;
      getExpressionConstants(unaryOp.getOperand(), stateSet);
    } else if (e instanceof ExpressionVar) {
      return;
    } else if (e instanceof ExpressionConstant) {
      ExpressionConstant eConst = (ExpressionConstant) e;
      stateSet.add(eConst.getName());
    } else if (e instanceof ExpressionFunc) {
      ExpressionFunc eFunc = (ExpressionFunc) e;
      for (int i = 0; i < eFunc.getNumOperands(); i++) {
        getExpressionConstants(eFunc.getOperand(i), stateSet);
      }
    } else {
      System.out.println("WARNING: unsupported expression type found! " + e);
    }
  }

  void populateStateVars() {

    // get all global state variables
    for (int i = 0; i < mf.getNumGlobals(); i++) {
      Declaration decl = mf.getGlobal(i);

      stateVariables.add(decl.getName());
      //System.out.println("global:" + decl.getName());
    }

    // get all modules
    for (int i = 0; i < mf.getNumModules(); i++) {
      Module m = mf.getModule(i);

      modules.add(m.getName());
      moduleVarListMap.put(m.getName(), new ArrayList<String>());
      //System.out.println("module:" + m.getName());


      // extract state variables of module
      for (int j = 0; j < m.getNumDeclarations(); j++) {
        Declaration decl = m.getDeclaration(j);

        stateVariables.add(decl.getName());
        varModuleMap.put(decl.getName(), m.getName());
        //System.out.println(m.getName() + "->" + decl.getName());
        moduleVarListMap.get(m.getName()).add(decl.getName());
      }
    }
  }

  void populateFormulas() {
    for (int i = 0; i < mf.getFormulaList().size(); i++) {
      formulaExpressionMap.put(mf.getFormulaList().getFormulaName(i),
                               mf.getFormulaList().getFormula(i));
    }
  }

  void populateConstants() {

    ConstantList cList = mf.getConstantList();

    for (int i = 0; i < cList.size(); i++) {
      constantSet.add(cList.getConstantName(i));
    }

  }

  void populateCommands() {

    stateVarDependencies = new HashMap<>();
    constantDependencies = new HashMap<>();

    for (String stateVar : stateVariables) {
      stateVarDependencies.put(stateVar, new HashSet<String>());
      constantDependencies.put(stateVar, new HashSet<String>());
    }

    for (int i = 0; i < mf.getNumModules(); i++) {

      Module m = mf.getModule(i);

      for (int j = 0; j < m.getNumCommands(); j++) {
        Command c = m.getCommand(j);

        Expression guard = c.getGuard();
        HashSet<String> stateSet = new HashSet<>();
        getExpressionStateVars(guard, stateSet);
        // System.out.println(c.toString());
        // System.out.println("guard states:" + stateSet);

        Updates us = c.getUpdates();

        for (int k = 0; k < us.getNumUpdates(); k++) {
          Update u = us.getUpdate(k);

          for (int l = 0; l < u.getNumElements(); l++) {

            HashSet<String> dependencies = stateVarDependencies.get(u.getVar(l));
            HashSet<String> constants = constantDependencies.get(u.getVar(l));

            getExpressionStateVars(u.getExpression(l), dependencies);
            getExpressionConstants(u.getExpression(l), constants);
            //dependencies.remove(u.getVar(l));
          }
        }
        //System.out.println();
      }
    }
  }

  // compute number of guards that contains this state var
  int computeGuardNumber(String stateVar) {
    int gNumber = 0;
    for (int i = 0; i < mf.getNumModules(); i++) {
      Module m = mf.getModule(i);
      for (int j = 0; j < m.getNumCommands(); j++) {
        Command c = m.getCommand(j);
        Expression guard = c.getGuard();
        HashSet<String> stateSet = new HashSet<>();
        getExpressionStateVars(guard, stateSet);
        if (stateSet.contains(stateVar)) {
          gNumber++;
        }
      }
    }
    return gNumber;
  }

  // counts in how many different updates stateVar appears this includes every
  // summand of a probabilistic or non-deterministic choice
  int countVarUpdates(String stateVar) {
    int varUpdates = 0;

    for (int i = 0; i < mf.getNumModules(); i++) {
      Module m = mf.getModule(i);
      for (int j = 0; j < m.getNumCommands(); j++) {
        Command c = m.getCommand(j);
        Updates us = c.getUpdates();

        for (int k = 0; k < us.getNumUpdates(); k++) {
          Update u = us.getUpdate(k);

          for (int l = 0; l < u.getNumElements(); l++) {
            if (u.getVar(l).equals(stateVar)) {
              varUpdates++;
            }
          }
        }
      }
    }
    return varUpdates;
  }

  // counts in how many updates the value of stateVar is dependent on
  // dependencyVar
  int computeVarUpdateDependence(String stateVar, String dependencyVar) {
    int varUpdates = 0;

    for (int i = 0; i < mf.getNumModules(); i++) {
      Module m = mf.getModule(i);
      for (int j = 0; j < m.getNumCommands(); j++) {
        Command c = m.getCommand(j);
        Updates us = c.getUpdates();

        for (int k = 0; k < us.getNumUpdates(); k++) {
          Update u = us.getUpdate(k);

          for (int l = 0; l < u.getNumElements(); l++) {
            if (u.getVar(l).equals(stateVar)) {
              HashSet<String> dependencies = new HashSet<>();
              getExpressionStateVars(u.getExpression(l), dependencies);
              if (dependencies.contains(dependencyVar)) {
                varUpdates++;
              }
            }
          }
        }
      }
    }
    return varUpdates;
  }

  // counts in how many guards the value of stateVar appears together with
  // dependencyVar
  int computeGuardDependence(String stateVar, String dependencyVar) {
    int varGuards = 0;

    for (int i = 0; i < mf.getNumModules(); i++) {
      Module m = mf.getModule(i);
      for (int j = 0; j < m.getNumCommands(); j++) {
        Command c = m.getCommand(j);
        Expression g = c.getGuard();

        HashSet<String> guardVars = new HashSet<>();
        getExpressionStateVars(g, guardVars);
        if (guardVars.contains(stateVar) && guardVars.contains(dependencyVar)) {
          varGuards++;
        }
      }
    }
    return varGuards;
  }

  PrismAnalyse(ModulesFile mf) {
    this.mf = mf;

    stateVariables = new HashSet<>();
    varModuleMap = new HashMap<>();
    moduleVarListMap = new HashMap<>();
    formulaExpressionMap = new HashMap<>();
    modules = new HashSet<>();
    constantSet = new HashSet<>();

  }

  void showDependencies() {

    for (String stateVar : stateVariables) {
      HashSet<String> dependencies = stateVarDependencies.get(stateVar);
      HashSet<String> constants = constantDependencies.get(stateVar);
      if (dependencies.size() == 0 && constants.size() > 0) {
        System.out.println(stateVar + "' uses constants " + constantDependencies.get(stateVar));
      } else if (dependencies.size() == 0 && constants.size() == 0) {
        System.out.println(stateVar + ": WARNING: should be declared constant");
      }
    }
  }

  ArrayList<StateMetric> computeGuardNumbers() {

    ArrayList<StateMetric> gNumbers = new ArrayList<>();
    for (String stateVar : stateVariables) {
      int guardNumber = computeGuardNumber(stateVar);
      StateMetric g = new StateMetric(stateVar, guardNumber);
      gNumbers.add(g);
    }

    return gNumbers;
  }

  ArrayList<StateMetric> computeVarUpdates() {

    ArrayList<StateMetric> uNumbers = new ArrayList<>();
    for (String stateVar : stateVariables) {
      int varUpdates = countVarUpdates(stateVar);
      StateMetric u = new StateMetric(stateVar, varUpdates);
      uNumbers.add(u);
    }
    return uNumbers;
  }

  ArrayList<StateMetric> computeGuardDependence() {

    ArrayList<StateMetric> guardNumbers = new ArrayList<>();
    for (String depVar : stateVariables) {
      int varGuards = 0;
      for (String stateVar : stateVariables) {
        int nVarUpdates = computeGuardDependence(stateVar, depVar);
        varGuards += nVarUpdates;
      }
      StateMetric g = new StateMetric(depVar, varGuards);
      guardNumbers.add(g);
    }
    return guardNumbers;
  }

  ArrayList<StateMetric> computeVarUpdateDependence() {

    ArrayList<StateMetric> uNumbers = new ArrayList<>();
    for (String depVar : stateVariables) {
      int varUpdates = 0;
      for (String stateVar : stateVariables) {
        int nVarUpdates = computeVarUpdateDependence(stateVar, depVar);
        varUpdates += nVarUpdates;
      }
      StateMetric u = new StateMetric(depVar, varUpdates);
      uNumbers.add(u);
    }
    return uNumbers;
  }


  void calcWeights(Update u, double wFather, int nSiblings, HashSet<String> statesExcl, HashMap<Expression, Double> nodeWeightMap) {

    double weight = wFather/nSiblings;
    int elements = u.getNumElements();

    for (int i = 0; i < elements; i++) {
      String var = u.getVar(i);
      HashSet<String> stateVars = new HashSet<>();
      getExpressionStateVars(u.getExpression(i), stateVars);
      for (String stateVar : statesExcl) {
        stateVars.remove(stateVar);
      }
      if (!statesExcl.contains(var) && stateVars.size() > 0) {
        ExpressionVar ev = new ExpressionVar(u.getVar(i), TypeInt.getInstance());
        nodeWeightMap.put(ev, weight / 2);
        calcWeights(u.getExpression(i), weight, 2, statesExcl, nodeWeightMap);
      } else if (!statesExcl.contains(var)) {
        ExpressionVar ev = new ExpressionVar(u.getVar(i), TypeInt.getInstance());
        nodeWeightMap.put(ev, weight);
      } else if (stateVars.size() > 0) {
        calcWeights(u.getExpression(i), weight, 1, statesExcl, nodeWeightMap);
      }
    }

  }

  void calcWeights(Command c, double wFather, int nSiblings, HashSet<String> statesExcl, HashMap<Expression, Double> nodeWeightMap) {

    double weight = wFather/nSiblings;

    Expression guard = c.getGuard();
    HashSet<String> stateSet = new HashSet<>();

    getExpressionStateVars(guard, stateSet);

    for (String stateVar : statesExcl) {
      stateSet.remove(stateVar);
    }

    int guardSize = stateSet.size();

    stateSet = new HashSet<>();

    Updates us = c.getUpdates();

    int updateChildren = 0;
    for (int i = 0; i < us.getNumUpdates(); i++) {
      Update u = us.getUpdate(i);

      boolean isEmptyUpdate = true;
      for (int j = 0; j < u.getNumElements(); j++) {
        if (!statesExcl.contains(u.getVar(j))) {
          stateSet.add(u.getVar(j));
          isEmptyUpdate = false;
        }
      }
      if (!isEmptyUpdate) {
        updateChildren++;
      }
    }

    //int updateChildren = stateSet.size();

    if (guardSize > 0 && updateChildren > 0) {
      calcWeights(guard, weight, 1 + updateChildren, statesExcl, nodeWeightMap);
      calcWeights(us, weight, 1 + updateChildren, statesExcl, nodeWeightMap);
    } else if (guardSize > 0) {
      calcWeights(guard, weight, 1, statesExcl, nodeWeightMap);
    } else if (updateChildren > 0) {
      calcWeights(us, weight, updateChildren, statesExcl, nodeWeightMap);
    }
  }

  void calcWeights(Updates us, double wFather, int nSiblings, HashSet<String> statesExcl, HashMap<Expression, Double> nodeWeightMap) {

    double weight = wFather/nSiblings;
    HashSet<String> stateSet = new HashSet<>();

    for (int i = 0; i < us.getNumUpdates(); i++) {
      Update u = us.getUpdate(i);

      for (int j = 0; j < u.getNumElements(); j++) {
        stateSet.add(u.getVar(j));
      }
    }

    for (String stateVar : statesExcl) {
      stateSet.remove(stateVar);
    }

    int children = stateSet.size();

    for (int i = 0; i < us.getNumUpdates(); i++) {
      Update u = us.getUpdate(i);

      for (int j = 0; j < u.getNumElements(); j++) {
        if (!statesExcl.contains(u.getVar(j))) {
          calcWeights(u, weight, 1, statesExcl, nodeWeightMap);
        }
      }
    }
  }

  // calculate weight of nodes, excluding all stateVars in statesExcl, resulting
  // in a mapping of stateVars to weight values
  //
  // this is resursive, the weight of the father and the number of children is
  // specified
  void calcWeights(Expression e, double wFather, int nSiblings, HashSet<String> statesExcl, HashMap<Expression, Double> nodeWeightMap) {

    if (e instanceof ExpressionConstant) {
      return;
    }

    double weight = wFather / nSiblings;

    HashSet<String> stateVars;

    if (e instanceof ExpressionBinaryOp) {
      stateVars = new HashSet<>();
      getExpressionStateVars(((ExpressionBinaryOp) e).getOperand1(), stateVars);
      for (String stateVar : statesExcl) {
        stateVars.remove(stateVar);
      }
      int op1 = stateVars.size();
      stateVars = new HashSet<>();
      getExpressionStateVars(((ExpressionBinaryOp) e).getOperand2(), stateVars);
      for (String stateVar : statesExcl) {
        stateVars.remove(stateVar);
      }
      int op2 = stateVars.size();
      if (op1 > 0 && op2 > 0) {
        calcWeights(((ExpressionBinaryOp) e).getOperand1(), weight, 2, statesExcl, nodeWeightMap);
        calcWeights(((ExpressionBinaryOp) e).getOperand2(), weight, 2, statesExcl, nodeWeightMap);
      } else if (op1 > 0) {
        calcWeights(((ExpressionBinaryOp) e).getOperand1(), weight, 1, statesExcl, nodeWeightMap);
      } else if (op2 > 0) {
        calcWeights(((ExpressionBinaryOp) e).getOperand2(), weight, 1, statesExcl, nodeWeightMap);
      }
    } else if (e instanceof ExpressionUnaryOp) {
      stateVars = new HashSet<>();
      getExpressionStateVars(((ExpressionUnaryOp) e).getOperand(), stateVars);
      for (String stateVar : statesExcl) {
        stateVars.remove(stateVar);
      }
      int op = stateVars.size();
      if (op > 0) {
        calcWeights(((ExpressionUnaryOp) e).getOperand(), weight, 1, statesExcl, nodeWeightMap);
      }
    } else if (e instanceof ExpressionVar) {
      nodeWeightMap.put(e, weight);
    } else if (e instanceof ExpressionFunc) {
      ExpressionFunc eFunc = (ExpressionFunc) e;

      int children = 0;
      for (int i = 0; i < eFunc.getNumOperands(); i++) {
        stateVars = new HashSet<>();
        getExpressionStateVars(eFunc.getOperand(i), stateVars);
        for (String stateVar : statesExcl) {
          stateVars.remove(stateVar);
        }
        int op = stateVars.size();
        if (op > 0) {
          children++;
        }
      }

      for (int i = 0; i < eFunc.getNumOperands(); i++) {
        stateVars = new HashSet<>();
        getExpressionStateVars(eFunc.getOperand(i), stateVars);
        for (String stateVar : statesExcl) {
          stateVars.remove(stateVar);
        }
        int op = stateVars.size();
        if (op > 0) {
          calcWeights(eFunc.getOperand(i), weight, children, statesExcl, nodeWeightMap);
        }
      }
    } else {
      System.out.println("WARNING: expression " + e.toString() + " not supported yet");
    }
  }

  LinkedList<String> rankVariables() {

    LinkedList<String> varList = new LinkedList<>();
    
    int commands = 0;
    for (int i = 0; i < mf.getNumModules(); i++) {
      Module m = mf.getModule(i);
      commands += m.getNumCommands();
    }

    HashSet<String> statesExcl = new HashSet<>();

    while(true) {

      HashMap<Expression, Double> nodeWeightMap = new HashMap<>();

      for (int i = 0; i < mf.getNumModules(); i++) {
        Module m = mf.getModule(i);

        for (int j = 0; j < m.getNumCommands(); j++) {
          calcWeights(m.getCommand(j), 1, m.getNumCommands(), statesExcl, nodeWeightMap);
        }
      }

      if (nodeWeightMap.size() == 0) {
        break;
      }

      double max = 0;
      String maxStateVar = null;

      for (Expression key : nodeWeightMap.keySet()) {
        if (key instanceof ExpressionVar) {
          double keyVal = nodeWeightMap.get(key);
          if (keyVal >= max) {
            max = keyVal;
            maxStateVar = ((ExpressionVar) key).getName();
          }
        }
      }

      String mStateVar = new String(maxStateVar);
      
      statesExcl.add(maxStateVar);
      //System.out.println("size: " + nodeWeightMap.size() + "\n" + nodeWeightMap);
      System.out.println("// variable " + mStateVar + " with value " + max);
      varList.push(mStateVar);
      //System.out.println(varList);
    }

    LinkedList<String> resultList = new LinkedList<>();
    for (String varName : varList) {
      //System.out.println(varName);
      resultList.push(varName);
    }

    return resultList;
  }

  void makeVarGlobal(ModulesFile mf, String varName) {
    if (!mf.isGlobalVariable(varName)) {
      
      // search module with this variable
      for (int i = 0; i < mf.getNumModules(); i++) {
        Module m = mf.getModule(i);

        List<Declaration> decls = m.getDeclarations();
        int index;
        for (index = 0; index < decls.size(); index++) {
          if (decls.get(index).getName().equals(varName)) {
            Declaration varDecl = decls.remove(index);
            mf.addGlobal(varDecl);
          }
        }
      }
    }
  }

  public static void main(String[] args) {

    PrismAnalyse bddOpt;

    try {
      PrismParser p = new PrismParser();
      FileInputStream fis = new FileInputStream(args[0]);
      ModulesFile mf = p.parseModulesFile(fis);

      mf.tidyUp();
      bddOpt = new PrismAnalyse(mf);

      LinkedList<String> varList = bddOpt.rankVariables();
      
      for (String varName : varList) {
        bddOpt.makeVarGlobal(mf, varName);
      }

      System.out.println(mf.toString());

    } catch(Exception e) {
      System.out.println("exception " + e);
    }
  }
}

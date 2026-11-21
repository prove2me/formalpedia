-- Prove2me | solution 1 for RungeKuttaOrderConditions.Butcher.dp_order5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:59:26.552026+00:00
-- url     : https://prove2.me/submissions/cd0f0b1f-2cc7-4d80-b63b-ba6352c68ba5

module
public import Mathlib.Algebra.Ring.Rat
public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.ToAdditive
public meta import Mathlib.Tactic.ToDual
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_RungeKuttaOrderConditions_ButcherOrder
public import Theorems.Thm_RungeKuttaOrderConditions_Butcher_satisfiesOrderConditions_iff
section
@[expose] public section
namespace RungeKuttaOrderConditions
namespace Q15
end Q15
namespace Z15
end Z15
namespace Butcher
end Butcher
end RungeKuttaOrderConditions
namespace RungeKuttaOrderConditions.Butcher
end Butcher
end RungeKuttaOrderConditions
namespace RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
end Butcher
end RungeKuttaOrderConditions
namespace RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
end Butcher
end RungeKuttaOrderConditions
namespace RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
private theorem catalogFiveEq : catalog 5 = treesUpToFive := rfl
private theorem dpCondition01 : orderCond dpA dpB t1 := by
  decide +kernel
private theorem dpCondition02 : orderCond dpA dpB t2 := by
  decide +kernel
private theorem dpCondition03 : orderCond dpA dpB t31 := by
  decide +kernel
private theorem dpCondition04 : orderCond dpA dpB t41 := by
  decide +kernel
private theorem dpCondition05 : orderCond dpA dpB t5bushy := by
  decide +kernel
private theorem dpCondition06 :
    orderCond dpA dpB (.node [leaf, leaf, .node [leaf]]) := by
  decide +kernel
private theorem dpCondition07 : orderCond dpA dpB t42 := by
  decide +kernel
private theorem dpCondition08 :
    orderCond dpA dpB (.node [leaf, .node [leaf], leaf]) := by
  decide +kernel
private theorem dpCondition09 :
    orderCond dpA dpB (.node [leaf, .node [leaf, leaf]]) := by
  decide +kernel
private theorem dpCondition10 :
    orderCond dpA dpB (.node [leaf, .node [.node [leaf]]]) := by
  decide +kernel
private theorem dpCondition11 : orderCond dpA dpB t32 := by
  decide +kernel
private theorem dpCondition12 :
    orderCond dpA dpB (.node [.node [leaf], leaf]) := by
  decide +kernel
private theorem dpCondition13 :
    orderCond dpA dpB (.node [.node [leaf], leaf, leaf]) := by
  decide +kernel
private theorem dpCondition14 :
    orderCond dpA dpB (.node [.node [leaf], .node [leaf]]) := by
  decide +kernel
private theorem dpCondition15 : orderCond dpA dpB t43 := by
  decide +kernel
private theorem dpCondition16 :
    orderCond dpA dpB (.node [.node [leaf, leaf], leaf]) := by
  decide +kernel
private theorem dpCondition17 :
    orderCond dpA dpB (.node [.node [leaf, leaf, leaf]]) := by
  decide +kernel
private theorem dpCondition18 :
    orderCond dpA dpB (.node [.node [leaf, .node [leaf]]]) := by
  decide +kernel
private theorem dpCondition19 : orderCond dpA dpB t44 := by
  decide +kernel
private theorem dpCondition20 :
    orderCond dpA dpB (.node [.node [.node [leaf]], leaf]) := by
  decide +kernel
private theorem dpCondition21 :
    orderCond dpA dpB (.node [.node [.node [leaf], leaf]]) := by
  decide +kernel
private theorem dpCondition22 :
    orderCond dpA dpB (.node [.node [.node [leaf, leaf]]]) := by
  decide +kernel
private theorem dpCondition23 :
    orderCond dpA dpB (.node [.node [.node [.node [leaf]]]]) := by
  decide +kernel
end Butcher
end RungeKuttaOrderConditions
end
end

set_option autoImplicit true
@[expose] public section
public section
open RungeKuttaOrderConditions RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
namespace RungeKuttaOrderConditions.Butcher
theorem _root_.solution : satisfiesOrderConditions dpA dpB 5 := by
  rw [satisfiesOrderConditions_iff, catalogFiveEq]; intro t ht
  fin_cases ht
  · exact dpCondition01
  · exact dpCondition02
  · exact dpCondition03
  · exact dpCondition04
  · exact dpCondition05
  · exact dpCondition06
  · exact dpCondition07
  · exact dpCondition08
  · exact dpCondition09
  · exact dpCondition10
  · exact dpCondition11
  · exact dpCondition12
  · exact dpCondition13
  · exact dpCondition14
  · exact dpCondition15
  · exact dpCondition16
  · exact dpCondition17
  · exact dpCondition18
  · exact dpCondition19
  · exact dpCondition20
  · exact dpCondition21
  · exact dpCondition22
  · exact dpCondition23
end RungeKuttaOrderConditions.Butcher

-- Prove2me | solution 1 for RungeKuttaOrderConditions.Butcher.orderCond_node_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:59:32.46641+00:00
-- url     : https://prove2.me/submissions/3ee0a92d-7bf1-49b3-bff5-177a6d9c6f68

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
public import Theorems.Thm_RungeKuttaOrderConditions_Butcher_Phi_node_perm
public import Theorems.Thm_RungeKuttaOrderConditions_Butcher_gamma_node_perm

set_option autoImplicit true
@[expose] public section
public section
open RungeKuttaOrderConditions RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
namespace RungeKuttaOrderConditions.Butcher
theorem _root_.solution (A : List (List ℚ)) (b : List ℚ) {F G : Forest} (h : F.Perm G) :
    orderCond A b (.node F) ↔ orderCond A b (.node G) := by
  unfold orderCond; rw [Phi_node_perm A b h, gamma_node_perm h]
end RungeKuttaOrderConditions.Butcher

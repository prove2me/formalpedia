-- Prove2me | solution 1 for RungeKuttaOrderConditions.Butcher.Phi_node_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:59:06.229543+00:00
-- url     : https://prove2.me/submissions/aec5aefa-fa8c-4b05-bc81-c658fc96b8b4

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
public import Theorems.Thm_RungeKuttaOrderConditions_Butcher_phiForest_perm

set_option autoImplicit true
@[expose] public section
public section
open RungeKuttaOrderConditions RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
namespace RungeKuttaOrderConditions.Butcher
theorem _root_.solution (A : List (List ℚ)) (b : List ℚ) {F G : Forest} (h : F.Perm G) :
    Phi A b (.node F) = Phi A b (.node G) := by
  simp only [Phi, phiVec]; rw [phiForest_perm A h]
end RungeKuttaOrderConditions.Butcher

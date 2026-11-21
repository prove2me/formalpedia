-- Prove2me | solution 1 for RungeKuttaOrderConditions.Butcher.phiForest_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:58:39.873178+00:00
-- url     : https://prove2.me/submissions/7320d585-b194-4d41-b004-70577a066129

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
public import Theorems.Thm_RungeKuttaOrderConditions_Butcher_pmul_comm
public import Theorems.Thm_RungeKuttaOrderConditions_Butcher_pmul_assoc

set_option autoImplicit true
@[expose] public section
public section
open RungeKuttaOrderConditions RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
namespace RungeKuttaOrderConditions.Butcher
theorem _root_.solution (A : List (List ℚ)) {F G : Forest} (h : F.Perm G) :
    phiForest A F = phiForest A G := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [phiForest]; rw [ih]
  | swap x y l =>
      simp only [phiForest]
      rw [← pmul_assoc,
        pmul_comm (mulMatVec A (phiVec A y)) (mulMatVec A (phiVec A x)),
        pmul_assoc]
  | trans _ _ ih1 ih2 => rw [ih1, ih2]
end RungeKuttaOrderConditions.Butcher

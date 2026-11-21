-- Prove2me | solution 1 for RungeKuttaOrderConditions.Butcher.gamma_node_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:58:50.303328+00:00
-- url     : https://prove2.me/submissions/9ba77a3d-8cce-4fbe-b192-a465a1e95022

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
public import Theorems.Thm_RungeKuttaOrderConditions_Butcher_orderF_perm
public import Theorems.Thm_RungeKuttaOrderConditions_Butcher_gammaF_perm

set_option autoImplicit true
@[expose] public section
public section
open RungeKuttaOrderConditions RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
namespace RungeKuttaOrderConditions.Butcher
theorem _root_.solution {F G : Forest} (h : F.Perm G) : gamma (.node F) = gamma (.node G) := by
  simp only [gamma, order]; rw [orderF_perm h, gammaF_perm h]
end RungeKuttaOrderConditions.Butcher

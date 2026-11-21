-- Prove2me | solution 1 for RungeKuttaOrderConditions.Butcher.gammaF_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:58:22.516418+00:00
-- url     : https://prove2.me/submissions/d7424909-6f66-449c-a904-a0c1b74161e1

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

set_option autoImplicit true
@[expose] public section
public section
open RungeKuttaOrderConditions RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
namespace RungeKuttaOrderConditions.Butcher
theorem _root_.solution {F G : Forest} (h : F.Perm G) : gammaF F = gammaF G := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [gammaF]; rw [ih]
  | swap x y l => simp only [gammaF]; ring
  | trans _ _ ih1 ih2 => rw [ih1, ih2]
end RungeKuttaOrderConditions.Butcher

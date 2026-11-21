-- Prove2me | solution 1 for RungeKuttaOrderConditions.Butcher.pmul_assoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:58:11.608301+00:00
-- url     : https://prove2.me/submissions/4492cca8-e3e2-4d2a-89ce-45bfacee0864

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
theorem _root_.solution : ∀ u v w : List ℚ, pmul (pmul u v) w = pmul u (pmul v w)
  | [],    _,     _     => by simp [pmul]
  | _::_,  [],    _     => by simp [pmul]
  | _::_,  _::_,  []    => by simp [pmul]
  | a::u,  b::v,  c::w  => by
      simp only [pmul, List.zipWith_cons_cons, mul_assoc]
      rw [← pmul, ← pmul, ← pmul, ← pmul, solution u v w]
end RungeKuttaOrderConditions.Butcher

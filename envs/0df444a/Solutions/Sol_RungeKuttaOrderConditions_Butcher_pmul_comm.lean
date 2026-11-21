-- Prove2me | solution 1 for RungeKuttaOrderConditions.Butcher.pmul_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:58:08.859643+00:00
-- url     : https://prove2.me/submissions/dd0c8284-37b4-4319-b758-c0470a4998a8

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
theorem _root_.solution : ∀ u v : List ℚ, pmul u v = pmul v u
  | [],    []    => rfl
  | [],    _::_  => rfl
  | _::_,  []    => rfl
  | a::u,  b::v  => by
      simp only [pmul, List.zipWith_cons_cons, mul_comm a b]
      rw [← pmul, ← pmul, solution u v]
end RungeKuttaOrderConditions.Butcher

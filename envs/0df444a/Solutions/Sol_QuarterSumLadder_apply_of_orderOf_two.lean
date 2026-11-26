-- Prove2me | solution 1 for QuarterSumLadder.apply_of_orderOf_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:59:00.587352+00:00
-- url     : https://prove2.me/submissions/bff2fdec-eb07-45b2-9714-d7da49c09d77

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_QuarterSumLadder_Basic

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution (χ : MulChar (ZMod p) GaussianInt) (hχ : orderOf χ = 2)
    (a : ZMod p) : χ a = 0 ∨ χ a = 1 ∨ χ a = -1 := by
  by_cases ha : a = 0
  · left; rw [ha]; exact MulChar.map_zero χ
  · right
    have : χ a * χ a = 1 := by
      rw [← sq, ← MulChar.pow_apply' χ (by norm_num), ← hχ, pow_orderOf_eq_one]
      exact MulChar.one_apply (Ne.isUnit ha)
    exact mul_self_eq_one_iff.1 this
end QuarterSumLadder

-- Prove2me | solution 1 for QuarterSumLadder.unit_apply_pow_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:54:27.659812+00:00
-- url     : https://prove2.me/submissions/801676b7-17c2-428c-83ba-01d96e018080

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
theorem _root_.solution {R : Type*} [CommRing R] (χ : MulChar (ZMod p) R) (hχ : orderOf χ = 4)
    (u : (ZMod p)ˣ) : χ u ^ 4 = 1 := by
  rw [← MulChar.pow_apply' χ (by norm_num), ← hχ, pow_orderOf_eq_one, MulChar.one_apply_coe]
end QuarterSumLadder

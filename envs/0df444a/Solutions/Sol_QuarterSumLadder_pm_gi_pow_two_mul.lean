-- Prove2me | solution 1 for QuarterSumLadder.pm_gi_pow_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:55:47.849255+00:00
-- url     : https://prove2.me/submissions/52d8f912-67e9-4d98-a6b0-44a35458880c

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_QuarterSumLadder_Basic
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_sq
attribute [local simp] QuarterSumLadder.gi_re
attribute [local simp] QuarterSumLadder.gi_im

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
namespace QuarterSumLadder
theorem _root_.solution {u : GaussianInt} (hu : u = gi ∨ u = -gi) (j : ℕ) :
    u ^ (2 * j) = (-1) ^ j := by
  have hu2 : u ^ 2 = -1 := by rcases hu with rfl | rfl <;> simp [gi_sq]
  rw [pow_mul, hu2]
end QuarterSumLadder

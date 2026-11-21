-- Prove2me | solution 1 for ReLUBinaryDepth.ProductTradeoff.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:40:03.923559+00:00
-- url     : https://prove2.me/submissions/e119e38a-b499-4a41-9055-aeeb0ebcae3f

import Mathlib
import Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Product

section
set_option autoImplicit false

namespace ReLUBinaryDepth.ProductTradeoff

theorem chk_lemma_2_1 (B M : ℝ) (θ : Bool → ℝ) (hB : 1 < B)
    (hθ : ∀ b, 0 ≤ θ b ∧ θ b ≤ B) :
    ∀ a : ℝ, 0 ≤ a → B * a ≤ M →
      selector θ M false a = a * θ false ∧
      selector θ M true a = a * θ true := by
  intro a ha hM
  obtain ⟨h0, h0'⟩ := hθ false
  obtain ⟨h1, h1'⟩ := hθ true
  have k0 : a * θ false ≤ M := by nlinarith [mul_le_mul_of_nonneg_left h0' ha]
  have k1 : a * θ true ≤ M := by nlinarith [mul_le_mul_of_nonneg_left h1' ha]
  have p0 : 0 ≤ a * θ false := mul_nonneg ha h0
  have p1 : 0 ≤ a * θ true := mul_nonneg ha h1
  constructor
  · simp only [selector, bit, relu]
    simp
    rw [max_eq_right p0, max_eq_left (by linarith)]
    ring
  · simp only [selector, bit, relu]
    simp
    rw [max_eq_left (by linarith), max_eq_right p1]
    ring

end ReLUBinaryDepth.ProductTradeoff
end

theorem solution : type_of% @ReLUBinaryDepth.ProductTradeoff.chk_lemma_2_1 := @ReLUBinaryDepth.ProductTradeoff.chk_lemma_2_1

-- Prove2me | solution 1 for WassFSG.Grad.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T19:33:46.556188+00:00
-- url     : https://prove2.me/submissions/1df52a91-4054-4ef9-95d8-47a4f23c24b8

import Mathlib

set_option autoImplicit false

theorem solution (A B r₀ : ℝ) (hA : 0 < A) (hB : 0 < B) (hr₀ : 0 ≤ r₀)
    (hsol : B * Real.sqrt r₀ + A = r₀)
    (hlargest : ∀ r : ℝ, 0 ≤ r → B * Real.sqrt r + A = r → r ≤ r₀) :
    B ^ 2 ≤ r₀ ∧ r₀ ≤ 2 * A + B ^ 2 := by
  have hs0 : 0 ≤ Real.sqrt r₀ := Real.sqrt_nonneg _
  have hs2 : Real.sqrt r₀ ^ 2 = r₀ := Real.sq_sqrt hr₀
  set s := Real.sqrt r₀ with hs
  have hsB : B < s := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonneg hs0 (sub_nonneg.2 hc)]
  constructor
  · nlinarith
  · nlinarith [sq_nonneg (s - B)]

-- Prove2me | solution 1 for QMCProduct.HalfApprox.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T19:30:30.695091+00:00
-- url     : https://prove2.me/submissions/b3e78cc9-0929-4ae0-a2c4-16b835c62d91

import Mathlib
import Definitions.Def_QMCProduct_HalfApprox_Basic

open QMCProduct.HalfApprox

theorem solution (p q r : ℝ) (hM : (swapGram p q r).PosSemidef) (hq : q ≤ 0) :
    -(Real.sqrt 3) / 2 ≤ p := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 3 := by positivity
  have h1 : 0 ≤ 3 + 6 * ((p + q + r - 1) / 2) := by
    have := hM.dotProduct_mulVec_nonneg ![0, 1, 1, 1]
    have e : star ![(0:ℝ), 1, 1, 1] ⬝ᵥ (swapGram p q r).mulVec ![0, 1, 1, 1]
        = 3 + 6 * ((p + q + r - 1) / 2) := by
      simp [swapGram, dotProduct, Matrix.mulVec, Fin.sum_univ_four]
      ring
    linarith
  have h2 : 0 ≤ 5 + 2 * Real.sqrt 3 * (p - r) - 2 * ((p + q + r - 1) / 2) := by
    have := hM.dotProduct_mulVec_nonneg ![Real.sqrt 3, 1, 0, -1]
    have e : star ![Real.sqrt 3, 1, 0, -1] ⬝ᵥ (swapGram p q r).mulVec ![Real.sqrt 3, 1, 0, -1]
        = 5 + 2 * Real.sqrt 3 * (p - r) - 2 * ((p + q + r - 1) / 2) := by
      simp [swapGram, dotProduct, Matrix.mulVec, Fin.sum_univ_four]
      ring_nf
      rw [hs]; ring
    linarith
  nlinarith [hs, hs0]

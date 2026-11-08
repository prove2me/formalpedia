-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rounded_ratio_lt
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-07T14:52:04.507592+00:00
-- url     : https://prove2.me/submissions/a9fcd07a-107c-4008-8ae2-8b671f4c9a4a

import Mathlib

/-- Replacement embedding: the rounded ratio is below `1 / A`. -/
theorem solution {A lam ell : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    (hround : A * lam < ell) : lam / ell < 1 / A := by
  have hell : 0 < ell := lt_trans (mul_pos hA hlam) hround
  rw [div_lt_iff₀ hell, div_mul_eq_mul_div, lt_div_iff₀ hA]
  nlinarith

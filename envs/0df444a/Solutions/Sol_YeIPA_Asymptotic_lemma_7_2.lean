-- Prove2me | solution 1 for YeIPA.Asymptotic.lemma_7_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:43:57.999371+00:00
-- url     : https://prove2.me/submissions/2e3342d7-1b90-48b3-a1cd-3d4a74b6969f

import Mathlib
import Definitions.Def_YeIPA_Asymptotic_LP

open Matrix
open YeIPA.Asymptotic

theorem g69c_term (x s dx ds : ℝ) (hx : 0 < x) (hs : 0 < s)
    (heq : x * ds + s * dx = -(x * s)) :
    (dx / Real.sqrt (x / s)) ^ 2 + (Real.sqrt (x / s) * ds) ^ 2 = x * s - 2 * (dx * ds) := by
  rw [div_pow, mul_pow, Real.sq_sqrt (div_nonneg hx.le hs.le)]
  have h2 : (x * ds + s * dx) ^ 2 = (x * s) ^ 2 := by rw [heq]; ring
  field_simp
  linear_combination h2

theorem solution {n : ℕ} (x s dx ds : Fin n → ℝ)
    (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j)
    (heq : ∀ j, x j * ds j + s j * dx j = -(x j * s j))
    (hmono : 0 ≤ dx ⬝ᵥ ds) :
    ∑ j, (dx j / scaling x s j) ^ 2 + ∑ j, (scaling x s j * ds j) ^ 2 ≤ x ⬝ᵥ s := by
  rw [← Finset.sum_add_distrib]
  unfold scaling
  rw [Finset.sum_congr rfl (fun j _ => g69c_term (x j) (s j) (dx j) (ds j) (hx j) (hs j) (heq j)),
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold dotProduct at hmono ⊢
  linarith

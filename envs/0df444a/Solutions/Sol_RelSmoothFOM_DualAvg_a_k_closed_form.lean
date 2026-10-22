-- Prove2me | solution 1 for RelSmoothFOM.DualAvg.a_k_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:24:27.538358+00:00
-- url     : https://prove2.me/submissions/383725ff-042b-49f3-9c0f-7760a2025202

import Mathlib
import Definitions.Def_RelSmoothFOM_DualAvg_Setting

set_option autoImplicit false
open RelSmoothFOM.DualAvg

theorem solution (L μ : ℝ) :
    (0 < μ → μ < L → ∀ k : ℕ, daSum L μ k = ((1 + μ / (L - μ)) ^ k - 1) / μ) ∧
    (μ = 0 → 0 < L → ∀ k : ℕ, daSum L μ k = (k : ℝ) / L) := by
  constructor
  · intro hμ hμL k
    have hd : L - μ ≠ 0 := by linarith
    have hr : 1 + μ / (L - μ) = L / (L - μ) := by field_simp; ring
    induction k with
    | zero => simp [daSum]
    | succ k ih =>
      have : daSum L μ (k + 1) = daSum L μ k + daWeight L μ k := by
        simp [daSum, Finset.sum_range_succ]
      rw [this, ih, daWeight, ← hr, pow_succ]
      generalize (1 + μ / (L - μ)) ^ k = X
      field_simp
      ring
  · intro hμ hL k
    subst hμ
    simp only [daSum, daWeight, sub_zero, div_self hL.ne', one_pow, mul_one,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp

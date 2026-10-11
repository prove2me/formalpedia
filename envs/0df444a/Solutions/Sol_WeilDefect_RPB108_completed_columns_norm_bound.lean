-- Prove2me | solution 1 for WeilDefect.RPB108.completed_columns_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T20:17:27.943164+00:00
-- url     : https://prove2.me/submissions/a739f73b-7fdd-45f1-a803-568937c3f020

import Mathlib
open scoped BigOperators
set_option autoImplicit false
theorem solution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : Fin 4 → E) (b : Fin 4 → ℝ) (hv : ∀ i, ‖v i‖ ≤ b i)
    (z : Fin 4 → ℂ) (h : E) :
    ‖(∑ i, z i • v i) + h‖ ≤ (∑ i, b i * ‖z i‖) + ‖h‖ := by
  calc
    ‖(∑ i, z i • v i) + h‖ ≤ ‖∑ i, z i • v i‖ + ‖h‖ := norm_add_le _ _
    _ ≤ (∑ i, ‖z i • v i‖) + ‖h‖ := add_le_add (norm_sum_le _ _) (le_refl _)
    _ ≤ (∑ i, b i * ‖z i‖) + ‖h‖ := by
      apply add_le_add _ (le_refl _)
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, mul_comm (b i)]
      exact mul_le_mul_of_nonneg_left (hv i) (norm_nonneg _)

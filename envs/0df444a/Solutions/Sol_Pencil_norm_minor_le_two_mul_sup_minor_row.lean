-- Prove2me | solution 1 for Pencil.norm_minor_le_two_mul_sup_minor_row
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/286036cb-c16c-5c4a-8a6c-f329ad26c36f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Pencil_norm_minor_le_two_mul_sup_minor_row

theorem solution {r : ℕ} (v w : Fin r → ℂ) {i₀ : Fin r}
    (hi₀ : ∀ i, ‖v i‖ ≤ ‖v i₀‖) (i j : Fin r) :
    ‖v i * w j - v j * w i‖ ≤ 2 * ⨆ l, ‖v i₀ * w l - v l * w i₀‖ := by
  set M := ⨆ l, ‖v i₀ * w l - v l * w i₀‖ with hM
  have hle : ∀ l, ‖v i₀ * w l - v l * w i₀‖ ≤ M := fun l ↦
    le_ciSup (Finite.bddAbove_range fun l ↦ ‖v i₀ * w l - v l * w i₀‖) l
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hle i₀)
  by_cases h0 : v i₀ = 0
  · have hv : ∀ k, v k = 0 := fun k ↦ by
      have hk := hi₀ k
      rw [h0, norm_zero] at hk
      exact norm_eq_zero.mp (le_antisymm hk (norm_nonneg _))
    have hz : v i * w j - v j * w i = 0 := by rw [hv i, hv j]; ring
    rw [hz, norm_zero]
    linarith
  · have hpos : 0 < ‖v i₀‖ := norm_pos_iff.mpr h0
    have key : v i₀ * (v i * w j - v j * w i)
        = v i * (v i₀ * w j - v j * w i₀) - v j * (v i₀ * w i - v i * w i₀) := by ring
    have h1 : ‖v i₀‖ * ‖v i * w j - v j * w i‖ ≤ ‖v i₀‖ * M + ‖v i₀‖ * M := by
      rw [← norm_mul, key]
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul]; exact mul_le_mul (hi₀ i) (hle j) (norm_nonneg _) (norm_nonneg _)
      · rw [norm_mul]; exact mul_le_mul (hi₀ j) (hle i) (norm_nonneg _) (norm_nonneg _)
    rw [← mul_add] at h1
    have h2 : ‖v i * w j - v j * w i‖ ≤ M + M := le_of_mul_le_mul_left h1 hpos
    linarith

end S_Pencil_norm_minor_le_two_mul_sup_minor_row
end P2MW
export P2MW.S_Pencil_norm_minor_le_two_mul_sup_minor_row (solution)

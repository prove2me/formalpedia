-- Prove2me | solution 1 for Pencil.norm_dotProduct_mul_sup_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/d7508700-45a8-572d-ba27-0e517c4cca70

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Pencil_norm_dotProduct_mul_sup_le

theorem solution {r : ℕ} (a v w : Fin r → ℂ) (hav : ∑ i, a i * v i = 0) :
    ‖∑ i, a i * w i‖ * (⨆ i, ‖v i‖)
      ≤ (∑ i, ‖a i‖) * ⨆ p : Fin r × Fin r, ‖v p.1 * w p.2 - v p.2 * w p.1‖ := by
  rcases isEmpty_or_nonempty (Fin r) with hr | hr
  · simp
  set S := ⨆ p : Fin r × Fin r, ‖v p.1 * w p.2 - v p.2 * w p.1‖ with hS_def
  have hS : ∀ p : Fin r × Fin r, ‖v p.1 * w p.2 - v p.2 * w p.1‖ ≤ S := fun p ↦
    le_ciSup (Finite.bddAbove_range fun p : Fin r × Fin r ↦ ‖v p.1 * w p.2 - v p.2 * w p.1‖) p
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun i ↦ ‖v i‖
  have hsup : (⨆ i, ‖v i‖) = ‖v i₀‖ :=
    le_antisymm (ciSup_le hi₀) (le_ciSup (Finite.bddAbove_range fun i ↦ ‖v i‖) i₀)
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS (i₀, i₀))
  have ha0 : 0 ≤ ∑ i, ‖a i‖ := Finset.sum_nonneg fun i _ ↦ norm_nonneg _
  rw [hsup]
  by_cases h0 : v i₀ = 0
  · rw [h0, norm_zero, mul_zero]; exact mul_nonneg ha0 hS0
  have key : v i₀ * ∑ i, a i * w i = ∑ i, a i * (v i₀ * w i - v i * w i₀) := by
    have h' : ∑ i, a i * (v i₀ * w i - v i * w i₀)
        = v i₀ * ∑ i, a i * w i - w i₀ * ∑ i, a i * v i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [h', hav, mul_zero, sub_zero]
  calc ‖∑ i, a i * w i‖ * ‖v i₀‖ = ‖v i₀ * ∑ i, a i * w i‖ := by rw [norm_mul, mul_comm]
    _ = ‖∑ i, a i * (v i₀ * w i - v i * w i₀)‖ := by rw [key]
    _ ≤ ∑ i, ‖a i * (v i₀ * w i - v i * w i₀)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖a i‖ * S := Finset.sum_le_sum fun i _ ↦ by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hS (i₀, i)) (norm_nonneg _)
    _ = (∑ i, ‖a i‖) * S := by rw [Finset.sum_mul]

end S_Pencil_norm_dotProduct_mul_sup_le
end P2MW
export P2MW.S_Pencil_norm_dotProduct_mul_sup_le (solution)

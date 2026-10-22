-- Prove2me | solution 1 for PESContracts.Linear.equation_7
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:37:39.179465+00:00
-- url     : https://prove2.me/submissions/16b5a99c-c43c-4862-af5d-9a49d57c593e

import Mathlib
import Definitions.Def_PESContracts_Linear_Model
set_option autoImplicit false
open MeasureTheory PESContracts.Linear

theorem solution (M : Params) (hM : M.Standing) (k : ℝ) (hk : 0 < k)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ M.typesᶜ = 0) :
    2 * ObjL M k μ (k / 2) =
      ∫ θ, (if θ ≤ θtilde M (k / 2)
        then k * θ * M.a0 + k ^ 2 / (2 * M.h)
        else k * M.a0) ∂μ := by
  obtain ⟨ha0, hh, -, -, -⟩ := hM
  have hpt : ∀ θ : ℝ, (if θ ≤ θtilde M (k / 2)
        then k * θ * M.a0 + k ^ 2 / (2 * M.h)
        else k * M.a0) = k * linAction M (k / 2) θ := by
    intro θ
    unfold linAction θtilde
    by_cases h : θ ≤ 1 - k / 2 / (M.h * M.a0)
    · have h1 : θ * M.a0 + k / 2 / M.h ≤ M.a0 := by
        have : θ * M.a0 ≤ (1 - k / 2 / (M.h * M.a0)) * M.a0 := mul_le_mul_of_nonneg_right h ha0.le
        have e : (1 - k / 2 / (M.h * M.a0)) * M.a0 = M.a0 - k / 2 / M.h := by
          field_simp
        linarith
      rw [if_pos h, min_eq_left h1]
      field_simp
    · push_neg at h
      have h1 : M.a0 ≤ θ * M.a0 + k / 2 / M.h := by
        have : (1 - k / 2 / (M.h * M.a0)) * M.a0 < θ * M.a0 := mul_lt_mul_of_pos_right h ha0
        have e : (1 - k / 2 / (M.h * M.a0)) * M.a0 = M.a0 - k / 2 / M.h := by
          field_simp
        linarith
      rw [if_neg (not_le.2 h), min_eq_right h1]
  simp_rw [hpt]
  rw [integral_const_mul]
  unfold ObjL
  ring

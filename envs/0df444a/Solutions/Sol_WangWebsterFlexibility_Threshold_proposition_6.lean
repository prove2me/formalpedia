-- Prove2me | solution 1 for WangWebsterFlexibility.Threshold.proposition_6
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T03:25:05.738907+00:00
-- url     : https://prove2.me/submissions/74978418-72fa-4977-807c-d81dc46c07de

import Mathlib
import Definitions.Def_WangWebsterFlexibility_Threshold_Benefits

open scoped NNReal
open MeasureTheory WangWebsterFlexibility.Threshold

theorem solution : ¬ (∀ (M : Model)
    (hπ₂ : 0 ≤ M.π₂) (hπ : M.π₂ < M.π₁)
    (hρ₀ : 0 ≤ M.ρ) (hρ₁ : M.ρ ≤ 1)
    (v : ℝ) (hv : 0 ≤ v) (s q₁ q₂ : ℝ≥0),
    (DeterministicFirst M → DP M v s q₁ q₂ = 0) ∧
    (s = 0 ∨ TotalDemandEndpoint M s → SD M v s q₁ q₂ = 0)) := by
  intro H
  let M : Model := ⟨⟨Measure.dirac 0, inferInstance⟩, ⟨Measure.dirac 2, inferInstance⟩, 2, 1, 0⟩
  have hdet : DeterministicFirst M := by
    refine ⟨0, ?_⟩
    show ∀ᵐ d ∂(Measure.dirac (0:ℝ≥0)), d = 0
    exact (ae_dirac_iff (measurableSet_singleton 0)).mpr rfl
  have h := (H M (by norm_num [M]) (by norm_num [M]) le_rfl zero_le_one 0 le_rfl 0 1 1).1 hdet
  have hlaw : M.law = Measure.dirac ((0:ℝ≥0), (2:ℝ≥0)) := by
    show (Measure.dirac (0:ℝ≥0)).prod (Measure.dirac (2:ℝ≥0)) = _
    exact Measure.dirac_prod_dirac
  simp only [DP, Model.expect, hlaw] at h
  rw [integral_dirac] at h
  simp [revenueFF, revenueDF, pos, M] at h
  norm_num at h

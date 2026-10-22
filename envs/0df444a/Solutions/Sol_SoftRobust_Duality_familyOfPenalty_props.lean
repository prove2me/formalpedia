-- Prove2me | solution 1 for SoftRobust.Duality.familyOfPenalty_props
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:16:16.021153+00:00
-- url     : https://prove2.me/submissions/ef4c2f14-169a-4178-8028-f0f3c017c922

import Mathlib
import Definitions.Def_SoftRobust_Duality_Mixture
import Definitions.Def_SoftRobust_Duality_ConvexRiskMeasure
import Definitions.Def_SoftRobust_Duality_Model

set_option autoImplicit false
open MeasureTheory
open scoped NNReal ENNReal
open SoftRobust.Duality

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (α : ProbabilityMeasure Ω → ℝ≥0∞) (hconv : IsConvexPenalty α)
    (hnorm : IsNormalizedPenalty α) :
    IsAdmissibleFamily (familyOfPenalty α) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ε₁ ε₂ h Q hQ
    have hQ' : α Q ≤ (ε₁ : ℝ≥0∞) := hQ
    show α Q ≤ (ε₂ : ℝ≥0∞)
    exact le_trans hQ' (by exact_mod_cast h)
  · intro ε₁ ε₂ Q₁ Q₂ t ht h₁ h₂
    have h₁' : α Q₁ ≤ (ε₁ : ℝ≥0∞) := h₁
    have h₂' : α Q₂ ≤ (ε₂ : ℝ≥0∞) := h₂
    show α (mix t ht Q₁ Q₂) ≤ ((t * ε₁ + (1 - t) * ε₂ : ℝ≥0) : ℝ≥0∞)
    calc α (mix t ht Q₁ Q₂) ≤ (t : ℝ≥0∞) * α Q₁ + ((1 - t : ℝ≥0) : ℝ≥0∞) * α Q₂ := hconv t ht Q₁ Q₂
      _ ≤ (t : ℝ≥0∞) * ε₁ + ((1 - t : ℝ≥0) : ℝ≥0∞) * ε₂ := by gcongr
      _ = ((t * ε₁ + (1 - t) * ε₂ : ℝ≥0) : ℝ≥0∞) := by push_cast; rfl
  · obtain ⟨Q, hQ⟩ := hnorm
    exact ⟨Q, show α Q ≤ ((0 : ℝ≥0) : ℝ≥0∞) by simp [hQ]⟩

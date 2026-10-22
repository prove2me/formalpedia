-- Prove2me | solution 1 for SoftRobust.Duality.penaltyOfFamily_familyOfPenalty
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:16:46.561331+00:00
-- url     : https://prove2.me/submissions/59f1be22-786b-426c-8f1a-d3ea508a1c1a

import Mathlib
import Definitions.Def_SoftRobust_Duality_Mixture
import Definitions.Def_SoftRobust_Duality_ConvexRiskMeasure
import Definitions.Def_SoftRobust_Duality_Model

set_option autoImplicit false
open MeasureTheory
open scoped NNReal ENNReal
open SoftRobust.Duality

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (α : ProbabilityMeasure Ω → ℝ≥0∞) :
    penaltyOfFamily (familyOfPenalty α) = α := by
  funext Q
  unfold penaltyOfFamily familyOfPenalty
  apply le_antisymm
  · by_cases h : α Q = ⊤
    · rw [h]; exact le_top
    · have h1 : α Q ≤ ((α Q).toNNReal : ℝ≥0∞) := by rw [ENNReal.coe_toNNReal h]
      calc (⨅ (ε : ℝ≥0) (_ : Q ∈ {Q | α Q ≤ (ε : ℝ≥0∞)}), (ε : ℝ≥0∞))
          ≤ ((α Q).toNNReal : ℝ≥0∞) := iInf₂_le (α Q).toNNReal h1
        _ = α Q := ENNReal.coe_toNNReal h
  · exact le_iInf₂ (fun ε hε => hε)

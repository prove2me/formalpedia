-- Prove2me | solution 1 for RiskPremiaDMP.Equivalence.risk_neutral_productivity
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T05:40:09.388654+00:00
-- url     : https://prove2.me/submissions/089af3ab-b26d-4fee-b682-eb72eb403e6b

import Mathlib
import Definitions.Def_RiskPremiaDMP_Equivalence_Model

open RiskPremiaDMP.Equivalence

theorem solution (P : RPParams) (hP : P.Standing) (y η BP : ℝ → ℝ)
    (hy : Continuous y) (hη : Continuous η) (h9 : SolvesPhysicalY P y BP) :
    SolvesRiskNeutralY P y η (riskNeutralBM η BP) := by
  intro t ht
  have hκ : P.κy ≠ 0 := ne_of_gt hP.1
  have h := h9 t ht
  have hint : ∫ u in (0 : ℝ)..t, P.κy * (-(P.σy / P.κy) * η u - y u)
      = (∫ u in (0 : ℝ)..t, -(P.σy * η u)) + ∫ u in (0 : ℝ)..t, -(P.κy * y u) := by
    rw [← intervalIntegral.integral_add]
    · apply intervalIntegral.integral_congr
      intro u _
      simp only
      field_simp
      ring
    · exact (continuous_const.mul hη).neg.intervalIntegrable 0 t
    · exact (continuous_const.mul hy).neg.intervalIntegrable 0 t
  have hB : riskNeutralBM η BP t - riskNeutralBM η BP 0 = (∫ u in (0 : ℝ)..t, η u) + (BP t - BP 0) := by
    simp [riskNeutralBM]; ring
  rw [hint, hB]
  have h2 : ∫ u in (0 : ℝ)..t, -(P.σy * η u) = -(P.σy * ∫ u in (0 : ℝ)..t, η u) := by
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
  rw [h2] at *
  linarith

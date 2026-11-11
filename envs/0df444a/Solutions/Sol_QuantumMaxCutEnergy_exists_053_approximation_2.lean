-- Prove2me | solution 2 for QuantumMaxCutEnergy.exists_053_approximation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T15:03:36.763924+00:00
-- url     : https://prove2.me/submissions/df661347-146f-4cd6-b409-846fb80c8f3b

import Theorems.Thm_QuantumMaxCutEnergy_agm_deterministic_product_value_program
import Theorems.Thm_QuantumMaxCutEnergy_agm_incident_floorValue_bounds
import Theorems.Thm_QuantumMaxCutEnergy_agm_numeric_candidate_combination

noncomputable section
open scoped BigOperators

namespace QMCDeterministicProductReduction
open QuantumMaxCutEnergy
open QMCNumericRuntime
open QMCNumericRuntime.EstimatorComposition

theorem exists_approximation (α : ℝ) (hα : α ≤ (0.53 : ℝ)) :
    ∃ A : Algorithm, PolynomialTime A ∧ ApproximationRatio A α := by
  obtain ⟨p, ⟨PA⟩, hp⟩ := agm_deterministic_product_value_program
  let P : Algorithm := { randomFactor := 0, randomDegree := 0, run := fun G _ => p G }
  let A : Algorithm := withFloor P IncidentRuntime.floorValue
  have hPA : OAI.MetricKMedian.Binary.PolyProgram encodeRequest
      OAI.MetricKMedian.Binary.Ratio.encode
      (fun request : Input × List Bool => (P.run request.1 request.2 : ℚ)) := PA
  refine ⟨A, withFloor_polynomialTime P IncidentRuntime.floorValue
    IncidentRuntime.floorRationalProgram hPA, ?_⟩
  intro G
  obtain ⟨hbsound, m, f, _hm, _hmf, _hfW, hupper, hforest, hmatching⟩ :=
    agm_incident_floorValue_bounds G
  let E : ℝ := ((max (IncidentRuntime.floorValue G) (p G) : ℚ≥0) : ℝ)
  have hbfloor : (IncidentRuntime.floorValue G : ℝ) ≤ E := by
    change (IncidentRuntime.floorValue G : ℝ) ≤
      ((max (IncidentRuntime.floorValue G) (p G) : ℚ≥0) : ℝ)
    exact_mod_cast le_max_left (IncidentRuntime.floorValue G) (p G)
  have hpvalue : (p G : ℝ) ≤ E := by
    change (p G : ℝ) ≤ ((max (IncidentRuntime.floorValue G) (p G) : ℚ≥0) : ℝ)
    exact_mod_cast le_max_right (IncidentRuntime.floorValue G) (p G)
  have hcomb := agm_numeric_candidate_combination (0.953 : ℝ)
    (∑ e, (G.weights e : ℝ)) m f (optimum G) E (by norm_num)
    hupper (hforest.trans hbfloor) (hmatching.trans hbfloor)
    ((hp G).2.trans hpvalue)
  have hO : 0 ≤ optimum G := (by positivity :
    (0 : ℝ) ≤ (IncidentRuntime.floorValue G : ℝ)).trans hbsound
  have hpoint : α * optimum G ≤ E := by
    have hscale := mul_le_mul_of_nonneg_right hα hO
    nlinarith only [hcomb, hscale, hO]
  constructor
  · intro r
    change ((max (IncidentRuntime.floorValue G) (p G) : ℚ≥0) : ℝ) ≤ optimum G
    rw [nnrat_max_cast]
    exact max_le hbsound (hp G).1
  · have hc : (Fintype.card (Fin (randomBits A G) → Bool) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    change α * optimum G ≤
      (∑ _r : Fin (randomBits A G) → Bool, E) /
        (Fintype.card (Fin (randomBits A G) → Bool) : ℝ)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [mul_div_cancel_left₀ _ hc]
    exact hpoint

end QMCDeterministicProductReduction


theorem solution :
    ∃ A : QuantumMaxCutEnergy.Algorithm,
      QuantumMaxCutEnergy.PolynomialTime A ∧
      QuantumMaxCutEnergy.ApproximationRatio A (0.53 : ℝ) :=
  QMCDeterministicProductReduction.exists_approximation (0.53 : ℝ) (by norm_num)

#print axioms solution

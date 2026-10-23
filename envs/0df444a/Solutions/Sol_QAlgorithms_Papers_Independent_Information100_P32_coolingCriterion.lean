-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P32.coolingCriterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:43:00.350674+00:00
-- url     : https://prove2.me/submissions/9dd28d93-7cc2-432f-ae94-7557664383c4

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P32 in
theorem solution (m : Model) (hp : 1 / 2 < m.pA) (hp1 : m.pA < 1)
    (hw : 0 < m.frequency) (hc : m.cA ≠ 0) (hK : 0 < denominatorK m)
    (hS : angleS m ≠ 0) :
    (m.pA < starPopulation m ↔ 0 < angleC m * differenceL m) ∧
    (starPopulation m < m.pA ↔ angleC m * differenceL m < 0) ∧
    (starPopulation m = m.pA ↔ angleC m * differenceL m = 0) := by
  have hq : 0 < Complex.normSq m.cA := Complex.normSq_pos.mpr hc
  have hpos : 0 < 2 * Complex.normSq m.cA / denominatorK m * (2 * m.pA - 1) := by
    apply mul_pos (div_pos (by linarith) hK); linarith
  have he : starPopulation m - m.pA =
      (2 * Complex.normSq m.cA / denominatorK m * (2 * m.pA - 1)) * (angleC m * differenceL m) := by
    unfold starPopulation; ring
  set x := angleC m * differenceL m
  set a := 2 * Complex.normSq m.cA / denominatorK m * (2 * m.pA - 1)
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · by_contra h'; push_neg at h'; nlinarith
  · nlinarith
  · by_contra h'; push_neg at h'; nlinarith
  · nlinarith
  · have : a * x = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact h
  · rw [h, mul_zero] at he; linarith

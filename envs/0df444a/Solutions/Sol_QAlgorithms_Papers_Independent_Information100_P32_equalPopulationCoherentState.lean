-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P32.equalPopulationCoherentState
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:35:50.834353+00:00
-- url     : https://prove2.me/submissions/a1912fcd-8fe2-4738-aa35-0733f7084130

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P32 in
theorem solution (m : Model) (hp : 1 / 2 < m.pA) (hp1 : m.pA < 1)
    (hw : 0 < m.frequency) (hc : m.cA ≠ 0) (hK : 0 < denominatorK m)
    (hS : angleS m ≠ 0) (heq : angleC m = Real.cos (m.frequency * m.duration)) :
    starPopulation m = m.pA ∧ starCoherence m ≠ 0 ∧
    (Real.sin (m.frequency * m.duration) = -angleS m →
      starCoherence m = m.cA * (2 * m.pA - 1 : ℝ) * (angleS m ^ 2 : ℝ) /
        (denominatorK m : ℂ)) := by
  have hL : differenceL m = 0 := by unfold differenceL; rw [heq]; ring
  have hKs : denominatorK m = Real.sin (m.frequency * m.duration) ^ 2 := by
    unfold denominatorK denominatorD; rw [hL]; ring
  have hsin : Real.sin (m.frequency * m.duration) ≠ 0 := by
    intro h; rw [hKs, h] at hK; norm_num at hK
  have hK0 : (denominatorK m : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  have hcoh : starCoherence m = -(m.cA / (denominatorK m : ℂ)) * (2 * m.pA - 1 : ℝ) *
      (angleS m : ℂ) * (Real.sin (m.frequency * m.duration) : ℂ) := by
    unfold starCoherence; rw [hL]; push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · unfold starPopulation; rw [hL]; ring
  · rw [hcoh]
    have h2 : ((2 * m.pA - 1 : ℝ) : ℂ) ≠ 0 := by
      have : (2 * m.pA - 1 : ℝ) ≠ 0 := by linarith
      exact_mod_cast this
    have h3 : (angleS m : ℂ) ≠ 0 := by exact_mod_cast hS
    have h4 : (Real.sin (m.frequency * m.duration) : ℂ) ≠ 0 := by exact_mod_cast hsin
    have h5 : m.cA / (denominatorK m : ℂ) ≠ 0 := div_ne_zero hc hK0
    simp only [neg_mul, ne_eq, neg_eq_zero, mul_eq_zero, not_or]
    exact ⟨⟨⟨h5, h2⟩, h3⟩, h4⟩
  · intro h
    rw [hcoh, h]
    push_cast
    field_simp

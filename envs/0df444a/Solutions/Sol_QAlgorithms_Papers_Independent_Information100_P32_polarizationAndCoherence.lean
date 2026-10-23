-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P32.polarizationAndCoherence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:45:59.861699+00:00
-- url     : https://prove2.me/submissions/78defb19-6ac3-425b-be03-e0174c6d064f

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P32 in
theorem solution (m : Model) (hK : 0 < denominatorK m) :
    0 < denominatorD m ∧ denominatorK m = denominatorD m * (1 - lambda m) ∧
    (2 * starPopulation m - 1) = (2 * m.pA - 1) / (1 - lambda m) ∧
    (m.pA ≠ 1 / 2 → (2 * starPopulation m - 1) / (2 * m.pA - 1) = 1 / (1 - lambda m)) ∧
    ‖phase m‖ = 1 ∧
    starCoherence m = -m.cA * (2 * m.pA - 1 : ℝ) * (angleS m : ℂ) /
      ((Real.sqrt (denominatorD m) * (1 - lambda m) : ℝ) : ℂ) * phase m ∧
    starCoherence m = -m.cA * (2 * starPopulation m - 1 : ℝ) * (angleS m : ℂ) /
      (Real.sqrt (denominatorD m) : ℂ) * phase m := by
  have hD0 : 0 ≤ denominatorD m := by
    unfold denominatorD; positivity
  have hD : 0 < denominatorD m := by
    rcases hD0.lt_or_eq with h | h
    · exact h
    · exfalso
      have h' : differenceL m ^ 2 + Real.sin (m.frequency * m.duration) ^ 2 = 0 := h.symm
      have hL : differenceL m = 0 := by
        nlinarith [sq_nonneg (differenceL m), sq_nonneg (Real.sin (m.frequency * m.duration))]
      have : denominatorK m = 0 := by
        unfold denominatorK; rw [hL, ← h]; ring
      linarith
  have hKl : denominatorK m = denominatorD m * (1 - lambda m) := by
    unfold denominatorK lambda; field_simp
  have hu : 0 < 1 - lambda m := by
    rw [hKl] at hK; exact pos_of_mul_pos_right hK hD.le
  have hpe : starPopulation m = m.pA + (2 * m.pA - 1) * lambda m / (2 * (1 - lambda m)) := by
    have e1 : starPopulation m = m.pA + (2 * m.pA - 1) * (4 * Complex.normSq m.cA * angleC m *
        differenceL m) / (2 * denominatorK m) := by
      unfold starPopulation; field_simp; ring
    rw [e1, hKl]; unfold lambda
    field_simp
  have h3 : 2 * starPopulation m - 1 = (2 * m.pA - 1) / (1 - lambda m) := by
    rw [hpe]; field_simp; ring
  set sD := Real.sqrt (denominatorD m) with hsD
  have hsDp : 0 < sD := Real.sqrt_pos.mpr hD
  have hsD2 : sD ^ 2 = denominatorD m := Real.sq_sqrt hD0
  set s := Real.sin (m.frequency * m.duration)
  set L := differenceL m
  have hDe : denominatorD m = L ^ 2 + s ^ 2 := rfl
  have hphase : phase m = ((s : ℂ) + Complex.I * (L : ℂ)) / (sD : ℂ) := rfl
  have hcoh : starCoherence m = -(m.cA / (denominatorK m : ℂ)) * (2 * m.pA - 1 : ℝ) *
      (angleS m : ℂ) * ((s : ℂ) + Complex.I * (L : ℂ)) := by
    unfold starCoherence; ring
  have hKc : (denominatorK m : ℂ) = (sD : ℂ) ^ 2 * ((1 - lambda m : ℝ) : ℂ) := by
    rw [hKl, ← hsD2]; push_cast; ring
  have hsDc : (sD : ℂ) ≠ 0 := by exact_mod_cast hsDp.ne'
  have huc : ((1 - lambda m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  refine ⟨hD, hKl, h3, ?_, ?_, ?_, ?_⟩
  · intro hp
    have : 2 * m.pA - 1 ≠ 0 := by intro h; apply hp; linarith
    rw [h3]; field_simp
  · rw [hphase, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsDp]
    rw [div_eq_one_iff_eq hsDp.ne', Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply, hDe]; ring
  · rw [hcoh, hphase, hKc]
    push_cast
    field_simp
  · rw [hcoh, hphase, hKc, h3]
    push_cast
    field_simp

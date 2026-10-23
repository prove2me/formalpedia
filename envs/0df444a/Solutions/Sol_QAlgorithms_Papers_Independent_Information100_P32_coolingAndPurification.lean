-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P32.coolingAndPurification
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:50:12.309173+00:00
-- url     : https://prove2.me/submissions/595180c9-5c72-47fd-9ec2-eccd6d0852b9

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

theorem X7_purity_rho (p : ℝ) (c : ℂ) :
    purity (rho p c) = p ^ 2 + (1 - p) ^ 2 + 2 * Complex.normSq c := by
  simp [purity, rho, Matrix.trace, Matrix.mul_apply, Complex.normSq_apply]
  ring

theorem X7_purity_star (m : Model) :
    purity (starState m) = m.pA ^ 2 + (1 - m.pA) ^ 2 +
        2 * (starPopulation m - m.pA) ^ 2 +
        2 * (starPopulation m - m.pA) * (2 * m.pA - 1) + 2 * Complex.normSq (starCoherence m) := by
  unfold starState; rw [X7_purity_rho]; ring

theorem X7_phys : Physical (3 / 4) (1 / 4) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [Complex.normSq_apply]; norm_num

/-- model with C = 0 -/
def X7_m2 : Model where
  coupling := Real.pi / 4
  frequency := Real.pi / 2
  duration := 1
  pA := 3 / 4
  cA := 1 / 4
  duration_pos := one_pos
  ancilla_physical := X7_phys

/-- model with C = 1/2, cos ωτ = 1 -/
def X7_m3 : Model where
  coupling := Real.pi / 6
  frequency := 2 * Real.pi
  duration := 1
  pA := 3 / 4
  cA := 1 / 4
  duration_pos := one_pos
  ancilla_physical := X7_phys

theorem X7_m2_vals : angleC X7_m2 = 0 ∧ angleS X7_m2 = 1 ∧
    Real.cos (X7_m2.frequency * X7_m2.duration) = 0 ∧
    Real.sin (X7_m2.frequency * X7_m2.duration) = 1 := by
  simp only [angleC, angleS, X7_m2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show 2 * (Real.pi / 4) * 1 = Real.pi / 2 by ring]; exact Real.cos_pi_div_two
  · rw [show 2 * (Real.pi / 4) * 1 = Real.pi / 2 by ring]; exact Real.sin_pi_div_two
  · rw [mul_one]; exact Real.cos_pi_div_two
  · rw [mul_one]; exact Real.sin_pi_div_two

theorem X7_m3_vals : angleC X7_m3 = 1 / 2 ∧ angleS X7_m3 = Real.sqrt 3 / 2 ∧
    Real.cos (X7_m3.frequency * X7_m3.duration) = 1 ∧
    Real.sin (X7_m3.frequency * X7_m3.duration) = 0 := by
  simp only [angleC, angleS, X7_m3]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show 2 * (Real.pi / 6) * 1 = Real.pi / 3 by ring]; exact Real.cos_pi_div_three
  · rw [show 2 * (Real.pi / 6) * 1 = Real.pi / 3 by ring]; exact Real.sin_pi_div_three
  · rw [mul_one]; exact Real.cos_two_pi
  · rw [mul_one]; exact Real.sin_two_pi

end QAlgorithms.Papers.Independent.Information100.P32

end

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P32 in
theorem solution :
    (∀ m : Model, 1 / 2 < m.pA → m.pA < 1 → 0 < m.frequency →
      0 < denominatorK m → angleS m ≠ 0 →
      purity (starState m) = m.pA ^ 2 + (1 - m.pA) ^ 2 +
        2 * (starPopulation m - m.pA) ^ 2 +
        2 * (starPopulation m - m.pA) * (2 * m.pA - 1) + 2 * Complex.normSq (starCoherence m) ∧
      (m.pA < starPopulation m → purity (rho m.pA 0) < purity (starState m))) ∧
    (∃ m : Model, 1 / 2 < m.pA ∧ m.pA < 1 ∧ 0 < m.frequency ∧
      0 < denominatorK m ∧ angleS m ≠ 0 ∧ starPopulation m = m.pA ∧
      purity (rho m.pA 0) < purity (starState m)) ∧
    (∃ m : Model, 1 / 2 < m.pA ∧ m.pA < 1 ∧ 0 < m.frequency ∧
      0 < denominatorK m ∧ angleS m ≠ 0 ∧ starPopulation m < m.pA ∧
      purity (rho m.pA 0) < purity (starState m)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m hp hp1 _ _ _
    refine ⟨X7_purity_star m, fun h => ?_⟩
    rw [X7_purity_star, X7_purity_rho]
    have := Complex.normSq_nonneg (starCoherence m)
    simp only [map_zero]
    nlinarith
  · obtain ⟨hC, hS, hc, hs⟩ := X7_m2_vals
    have hL : differenceL X7_m2 = 0 := by unfold differenceL; rw [hC, hc]; ring
    have hK : denominatorK X7_m2 = 1 := by
      unfold denominatorK denominatorD; rw [hL, hs, hC]; ring
    have hpop : starPopulation X7_m2 = 3 / 4 := by
      unfold starPopulation; rw [hC]; simp [X7_m2]
    have hcoh : starCoherence X7_m2 = -1 / 8 := by
      unfold starCoherence; rw [hK, hS, hL, hs]; simp [X7_m2]; norm_num
    refine ⟨X7_m2, by norm_num [X7_m2], by norm_num [X7_m2], ?_, by rw [hK]; norm_num,
      by rw [hS]; norm_num, by rw [hpop]; rfl, ?_⟩
    · simp only [X7_m2]; positivity
    · rw [X7_purity_star, X7_purity_rho, hpop, hcoh, Complex.normSq_apply]
      simp [X7_m2]
  · obtain ⟨hC, hS, hc, hs⟩ := X7_m3_vals
    have hL : differenceL X7_m3 = -1 / 2 := by unfold differenceL; rw [hC, hc]; ring
    have hq : Complex.normSq X7_m3.cA = 1 / 16 := by
      simp only [X7_m3]; rw [Complex.normSq_apply]; norm_num
    have hK : denominatorK X7_m3 = 5 / 16 := by
      unfold denominatorK denominatorD; rw [hL, hs, hC, hq]; norm_num
    have hpop : starPopulation X7_m3 = 3 / 4 - 1 / 20 := by
      unfold starPopulation; rw [hC, hL, hK, hq]; simp only [X7_m3]; norm_num
    have hcoh : starCoherence X7_m3 = Complex.I * ((Real.sqrt 3 / 10 : ℝ) : ℂ) := by
      unfold starCoherence; rw [hK, hS, hL, hs]; simp only [X7_m3]; push_cast; ring
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    refine ⟨X7_m3, by norm_num [X7_m3], by norm_num [X7_m3], ?_, by rw [hK]; norm_num,
      by rw [hS]; positivity, by rw [hpop]; simp only [X7_m3]; norm_num, ?_⟩
    · simp only [X7_m3]; positivity
    · rw [X7_purity_star, X7_purity_rho, hpop, hcoh, Complex.normSq_apply]
      simp only [X7_m3]
      simp
      nlinarith [h3]

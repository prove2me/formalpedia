-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P32.oppositeCosinePopulationBound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:35:52.818598+00:00
-- url     : https://prove2.me/submissions/c69bb43c-4524-480e-a923-a72a615dcfc9

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P32 in
theorem solution (m : Model) (hp : 1 / 2 < m.pA)
    (hp1 : m.pA < 1) (hw : 0 < m.frequency)
    (hC : angleC m = -1) (hb : Real.cos (m.frequency * m.duration) = 1) :
    starPopulation m = m.pA + Complex.normSq m.cA / (1 - 2 * Complex.normSq m.cA) *
      (2 * m.pA - 1) ∧
    starPopulation m ≤ m.pA + m.pA * (1 - m.pA) / (1 - 2 * m.pA * (1 - m.pA)) *
      (2 * m.pA - 1) := by
  obtain ⟨_, _, hq⟩ := m.ancilla_physical
  set q := Complex.normSq m.cA
  have hq0 : 0 ≤ q := Complex.normSq_nonneg _
  have hs : Real.sin (m.frequency * m.duration) = 0 := by
    have := Real.sin_sq_add_cos_sq (m.frequency * m.duration)
    rw [hb] at this; nlinarith
  have hL : differenceL m = -2 := by unfold differenceL; rw [hC, hb]; norm_num
  have hK : denominatorK m = 4 - 8 * q := by
    unfold denominatorK denominatorD; rw [hL, hs, hC]; ring
  have hq4 : 4 * q ≤ 1 := by nlinarith [sq_nonneg (2 * m.pA - 1)]
  have h1 : starPopulation m = m.pA + q / (1 - 2 * q) * (2 * m.pA - 1) := by
    unfold starPopulation; rw [hK, hC, hL]
    have : (1 - 2 * q) ≠ 0 := by linarith
    have : (4 - 8 * q) ≠ 0 := by linarith
    field_simp; ring
  refine ⟨h1, ?_⟩
  rw [h1]
  have hu : m.pA * (1 - m.pA) ≤ 1 / 4 := by nlinarith [sq_nonneg (2 * m.pA - 1)]
  have hmono : q / (1 - 2 * q) ≤ m.pA * (1 - m.pA) / (1 - 2 * (m.pA * (1 - m.pA))) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have : 2 * m.pA * (1 - m.pA) = 2 * (m.pA * (1 - m.pA)) := by ring
  rw [this]
  have := mul_le_mul_of_nonneg_right hmono (by linarith : (0:ℝ) ≤ 2 * m.pA - 1)
  linarith

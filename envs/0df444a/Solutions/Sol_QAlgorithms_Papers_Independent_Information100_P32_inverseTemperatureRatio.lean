-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P32.inverseTemperatureRatio
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:42:51.42209+00:00
-- url     : https://prove2.me/submissions/8d4f00d3-7c3b-4adc-81f2-f9f88bfae8bd

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

theorem X7_odds_lt {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    s / (1 - s) < t / (1 - t) ↔ s < t := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  constructor <;> intro h <;> nlinarith

theorem X7_odds_pos {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : 0 < s / (1 - s) :=
  div_pos hs0 (by linarith)

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P32 in
theorem solution (m : Model) (hp : 1 / 2 < m.pA) (hp1 : m.pA < 1)
    (hw : 0 < m.frequency) (hK : 0 < denominatorK m)
    (hs0 : 0 < starPopulation m) (hs1 : starPopulation m < 1) :
    inverseTemperature m.frequency (starPopulation m) =
      Real.log ((2 * m.pA - lambda m) / (2 * (1 - m.pA) - lambda m)) / m.frequency ∧
    inverseTemperature m.frequency (starPopulation m) / inverseTemperature m.frequency m.pA =
      Real.artanh ((2 * m.pA - 1) / (1 - lambda m)) / Real.artanh (2 * m.pA - 1) ∧
    (1 < inverseTemperature m.frequency (starPopulation m) / inverseTemperature m.frequency m.pA ↔
      m.pA < starPopulation m) ∧
    (inverseTemperature m.frequency (starPopulation m) / inverseTemperature m.frequency m.pA < 1 ↔
      starPopulation m < m.pA) := by
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
  set p := starPopulation m with hpdef
  set a := m.pA
  set l := lambda m
  have hl : 1 - l ≠ 0 := hu.ne'
  have hden : 2 * (1 - a) - l = 2 * (1 - l) * (1 - p) := by
    rw [hpe]; field_simp; ring
  have hnum : 2 * a - l = 2 * (1 - l) * p := by
    rw [hpe]; field_simp; ring
  have hY : (2 * a - l) / (2 * (1 - a) - l) = p / (1 - p) := by
    rw [hden, hnum]
    have : (1 - p) ≠ 0 := by linarith
    field_simp
  have hX : (1 + (2 * a - 1) / (1 - l)) / (1 - (2 * a - 1) / (1 - l)) = p / (1 - p) := by
    rw [← hY]
    have h2 : 2 * (1 - a) - l ≠ 0 := by
      rw [hden]; apply mul_ne_zero (by linarith) (by linarith)
    have h3 : 1 - l ≠ 0 := hu.ne'
    have e1 : 1 + (2 * a - 1) / (1 - l) = (2 * a - l) / (1 - l) := by
      field_simp; ring
    have e2 : 1 - (2 * a - 1) / (1 - l) = (2 * (1 - a) - l) / (1 - l) := by
      field_simp; ring
    rw [e1, e2, div_div_div_cancel_right₀ h3]
  have hZ : (1 + (2 * a - 1)) / (1 - (2 * a - 1)) = a / (1 - a) := by
    have : (1 - a) ≠ 0 := by linarith
    rw [show 1 + (2 * a - 1) = 2 * a by ring, show 1 - (2 * a - 1) = 2 * (1 - a) by ring]
    field_simp
  have hYp := X7_odds_pos hs0 hs1
  have hZp := X7_odds_pos (by linarith : 0 < a) hp1
  have hlogZ : 0 < Real.log (a / (1 - a)) := by
    apply Real.log_pos
    rw [one_lt_div (by linarith)]; linarith
  have hratio : inverseTemperature m.frequency p / inverseTemperature m.frequency a =
      Real.log (p / (1 - p)) / Real.log (a / (1 - a)) := by
    unfold inverseTemperature
    field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold inverseTemperature; rw [hY]
  · rw [hratio]
    unfold Real.artanh
    rw [hX, hZ, Real.log_sqrt hYp.le, Real.log_sqrt hZp.le]
    field_simp
  · rw [hratio, one_lt_div hlogZ, Real.log_lt_log_iff hZp hYp]
    exact X7_odds_lt (by linarith) hp1 hs0 hs1
  · rw [hratio, div_lt_one hlogZ, Real.log_lt_log_iff hYp hZp]
    exact X7_odds_lt hs0 hs1 (by linarith) hp1

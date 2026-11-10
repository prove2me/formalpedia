-- Prove2me | solution 1 for QiFixedDesign.Concentration.lemma_7
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T11:38:22.529984+00:00
-- url     : https://prove2.me/submissions/176cc091-ab0c-42a0-87f5-5c03e4f78b1b

import Mathlib
import Definitions.Def_QiFixedDesign_Concentration_ShiftedLaw
import Definitions.Def_QiFixedDesign_Concentration_Radii
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance

open MeasureTheory Matrix Filter Topology
open scoped ENNReal
open QiFixedDesign.Concentration

noncomputable def mu0 : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ) + (1 / 2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ)

instance : IsProbabilityMeasure mu0 := by
  refine ⟨?_⟩
  simp [mu0, ENNReal.inv_two_add_inv_two]

theorem solution : ¬ (∀ {p : ℕ} (x : ℕ → Fin p → ℝ) (β₀ : Fin p → ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (a A : ℝ) (hTail : LightTail μ a A) (hMean : ∫ u, u ∂μ = 0) (hDesign : GramLimit x) (c : Fin p → ℝ) (κ : ℝ) (hκ : (∫ u, u ^ 2 ∂μ) ≤ κ) (η : ℝ) (hη : 0 < η) (hη₁ : η < 1), Tendsto (radiusThree x c κ η) atTop (𝓝 0) ∧ ∀ N : ℕ, admissible x N → Measure.pi (fun _ : Fin N => μ) {ω | ENNReal.ofReal (radiusThree x c κ η N) ≤ WassersteinDRO.Duality.wassersteinDistance 1 μ (shiftedLaw μ x β₀ c ω)} ≤ ENNReal.ofReal η) := by
  intro H
  let x0 : ℕ → Fin 0 → ℝ := fun _ => ![]
  let b0 : Fin 0 → ℝ := ![]
  let c0 : Fin 0 → ℝ := ![]
  have hTail : LightTail mu0 2 (Real.exp 1) := by
    refine ⟨by norm_num, Real.one_lt_exp_iff.mpr zero_lt_one, ?_⟩
    unfold exponentialMoment mu0
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      lintegral_dirac, lintegral_dirac]
    have h1 : |(1 : ℝ)| ^ (2 : ℝ) = 1 := by norm_num
    have h2 : |(-1 : ℝ)| ^ (2 : ℝ) = 1 := by norm_num
    rw [h1, h2, ← add_smul, one_div, ENNReal.inv_two_add_inv_two, one_smul]
  have hMean : ∫ u, u ∂mu0 = 0 := by
    unfold mu0
    have hi1 : Integrable (fun u : ℝ => u) ((1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)) :=
      (integrable_dirac (by norm_num)).smul_measure (by norm_num)
    have hi2 : Integrable (fun u : ℝ => u) ((1 / 2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ)) :=
      (integrable_dirac (by norm_num)).smul_measure (by norm_num)
    rw [integral_add_measure hi1 hi2, integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac]
    norm_num
  have hDesign : GramLimit x0 := by
    refine ⟨0, ?_, ?_⟩
    · simp [Matrix.det_isEmpty]
    · have hconst : (fun N : ℕ => (N : ℝ)⁻¹ • gram x0 N) = fun _ => 0 := by
        ext N i j
        exact Fin.elim0 i
      rw [hconst]
      exact tendsto_const_nhds
  have hκ : (∫ u, u ^ 2 ∂mu0) ≤ 1 := by
    unfold mu0
    have hi1 : Integrable (fun u : ℝ => u ^ 2) ((1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)) :=
      (integrable_dirac (by norm_num)).smul_measure (by norm_num)
    have hi2 : Integrable (fun u : ℝ => u ^ 2) ((1 / 2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ)) :=
      (integrable_dirac (by norm_num)).smul_measure (by norm_num)
    rw [integral_add_measure hi1 hi2, integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac]
    norm_num
  have hadm : admissible x0 1 := by
    refine ⟨Nat.one_pos, ?_⟩
    simp [Matrix.det_isEmpty]
  have hconc := (H x0 b0 mu0 2 (Real.exp 1) hTail hMean hDesign c0 1 hκ (1 / 2) (by norm_num) (by norm_num)).2 1 hadm
  have hrad : radiusThree x0 c0 1 (1 / 2) 1 = 0 := by
    simp [radiusThree, c0]
  rw [hrad, ENNReal.ofReal_zero] at hconc
  have huniv : {ω : Fin 1 → ℝ | 0 ≤ WassersteinDRO.Duality.wassersteinDistance 1 mu0 (shiftedLaw mu0 x0 b0 c0 ω)} = Set.univ := by
    ext ω
    simp
  rw [huniv, measure_univ] at hconc
  have hlt : ENNReal.ofReal (1 / 2 : ℝ) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.mpr (by norm_num)
  exact not_le_of_gt hlt hconc

-- Prove2me | solution 2 for QiFixedDesign.Concentration.lemma_7
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-13T19:08:58.17622+00:00
-- url     : https://prove2.me/submissions/c8df788c-4605-4032-8b76-0b51f1b47387

import Mathlib
import Definitions.Def_QiFixedDesign_Concentration_ShiftedLaw
import Definitions.Def_QiFixedDesign_Concentration_Radii
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance

open MeasureTheory Matrix Filter Topology
open scoped ENNReal

open QiFixedDesign.Concentration

theorem solution : ¬ (∀ {p : ℕ} (x : ℕ → Fin p → ℝ) (β₀ : Fin p → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a A : ℝ) (hTail : LightTail μ a A) (hMean : ∫ u, u ∂μ = 0)
    (hDesign : GramLimit x)
    (c : Fin p → ℝ) (κ : ℝ) (hκ : (∫ u, u ^ 2 ∂μ) ≤ κ)
    (η : ℝ) (hη : 0 < η) (hη₁ : η < 1),
    Tendsto (radiusThree x c κ η) atTop (𝓝 0) ∧
    ∀ N : ℕ, admissible x N →
      Measure.pi (fun _ : Fin N => μ)
        {ω | ENNReal.ofReal (radiusThree x c κ η N) ≤
          WassersteinDRO.Duality.wassersteinDistance 1 μ (shiftedLaw μ x β₀ c ω)} ≤
        ENNReal.ofReal η) := by
  intro hall
  let x : ℕ → Fin 0 → ℝ := fun _ i => Fin.elim0 i
  let β₀ : Fin 0 → ℝ := Fin.elim0
  let c : Fin 0 → ℝ := Fin.elim0
  let μ₁ : Measure ℝ := (2⁻¹ : ℝ≥0∞) • Measure.dirac (-1 : ℝ)
  let μ₂ : Measure ℝ := (2⁻¹ : ℝ≥0∞) • Measure.dirac (1 : ℝ)
  let μ : Measure ℝ := μ₁ + μ₂
  have h2_inv_ne_top : (2⁻¹ : ℝ≥0∞) ≠ ⊤ := ENNReal.inv_ne_top.mpr (by norm_num)
  have hμ_prob : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    simp [μ, μ₁, μ₂, ENNReal.inv_two_add_inv_two]
  have hTail : LightTail μ 2 (Real.exp 1) := by
    refine ⟨by norm_num, Real.one_lt_exp_iff.mpr one_pos, ?_⟩
    dsimp [exponentialMoment, μ, μ₁, μ₂]
    have hm : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (|u| ^ (2 : ℝ)))) :=
      ENNReal.measurable_ofReal.comp
        (Real.continuous_exp.comp
          (continuous_abs.rpow_const fun _ => Or.inr (by norm_num))).measurable
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      lintegral_dirac' _ hm, lintegral_dirac' _ hm]
    have hneg : |-1| ^ (2 : ℝ) = (1 : ℝ) := by norm_num
    have hpos : |(1 : ℝ)| ^ (2 : ℝ) = (1 : ℝ) := by norm_num
    rw [hneg, hpos, smul_eq_mul, ← right_distrib, ENNReal.inv_two_add_inv_two, one_mul]
  have hMean : ∫ u, u ∂μ = 0 := by
    have hint1 : Integrable (fun u : ℝ => u) μ₁ :=
      (integrable_dirac (a := (-1 : ℝ)) (f := fun u : ℝ => u) (by simp)).smul_measure h2_inv_ne_top
    have hint2 : Integrable (fun u : ℝ => u) μ₂ :=
      (integrable_dirac (a := (1 : ℝ)) (f := fun u : ℝ => u) (by simp)).smul_measure h2_inv_ne_top
    dsimp [μ]
    rw [integral_add_measure hint1 hint2]
    dsimp [μ₁, μ₂]
    rw [integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
    simp [smul_eq_mul]
  have hDesign : GramLimit x := by
    refine ⟨(0 : Matrix (Fin 0) (Fin 0) ℝ), ?_, ?_⟩
    · simp
    · have hconst : (fun N : ℕ => (N : ℝ)⁻¹ • gram x N) =
          fun _ : ℕ => (0 : Matrix (Fin 0) (Fin 0) ℝ) := by
        ext N i j
        exact Fin.elim0 i
      rw [hconst]
      exact tendsto_const_nhds
  have hκ : (∫ u, u ^ 2 ∂μ) ≤ (1 : ℝ) := by
    have hint1 : Integrable (fun u : ℝ => u ^ 2) μ₁ :=
      (integrable_dirac (a := (-1 : ℝ)) (f := fun u : ℝ => u ^ 2) (by simp)).smul_measure
        h2_inv_ne_top
    have hint2 : Integrable (fun u : ℝ => u ^ 2) μ₂ :=
      (integrable_dirac (a := (1 : ℝ)) (f := fun u : ℝ => u ^ 2) (by simp)).smul_measure
        h2_inv_ne_top
    dsimp [μ]
    rw [integral_add_measure hint1 hint2]
    dsimp [μ₁, μ₂]
    rw [integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
    simp only [even_two.neg_pow, one_pow, smul_eq_mul, mul_one]
    have h2 : (2⁻¹ : ℝ≥0∞).toReal = (1 / 2 : ℝ) := by
      rw [ENNReal.toReal_inv]
      norm_num
    linarith
  have hadm : admissible x 1 := by
    refine ⟨Nat.zero_lt_one, ?_⟩
    simp
  have hspec := @hall 0 x β₀ μ hμ_prob 2 (Real.exp 1) hTail hMean hDesign
    c 1 hκ (1 / 2) (by norm_num) (by norm_num)
  have hN1 := hspec.2 1 hadm
  have hrad0 : radiusThree x c 1 (1 / 2) 1 = 0 := by
    simp [radiusThree, dotProduct]
  rw [hrad0, ENNReal.ofReal_zero] at hN1
  have hset : {ω : Fin 1 → ℝ | (0 : ℝ≥0∞) ≤
      WassersteinDRO.Duality.wassersteinDistance 1 μ
        (shiftedLaw μ x β₀ c ω)} = Set.univ := by
    ext ω
    simp
  rw [hset] at hN1
  have : IsProbabilityMeasure μ := hμ_prob
  have hpi_univ : Measure.pi (fun _ : Fin 1 => μ) Set.univ = 1 := measure_univ
  rw [hpi_univ] at hN1
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hN1
  rw [ENNReal.toReal_one, ENNReal.toReal_ofReal (by norm_num)] at hreal
  linarith

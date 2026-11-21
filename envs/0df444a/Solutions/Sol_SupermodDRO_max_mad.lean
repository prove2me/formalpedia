-- Prove2me | solution 1 for SupermodDRO.max_mad
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T03:55:53.585002+00:00
-- url     : https://prove2.me/submissions/95ca4856-260f-4e00-827c-da5aad222f8b

import Mathlib

open MeasureTheory

set_option maxHeartbeats 2000000

theorem solution (zl zu μ : ℝ) (hlt : zl < zu) (hμ : μ ∈ Set.Icc zl zu) :
    (∀ P : Measure ℝ, IsProbabilityMeasure P → P (Set.Icc zl zu) = 1 → ∫ z, z ∂P = μ →
      ∫ z, |z - μ| ∂P ≤ 2 * (zu - μ) * (μ - zl) / (zu - zl)) ∧
    ∃ P : Measure ℝ, IsProbabilityMeasure P ∧ P (Set.Icc zl zu) = 1 ∧ ∫ z, z ∂P = μ ∧
      ∫ z, |z - μ| ∂P = 2 * (zu - μ) * (μ - zl) / (zu - zl) := by
  have hd : 0 < zu - zl := by linarith
  have hdne : zu - zl ≠ 0 := hd.ne'
  constructor
  · intro P hPprob hPsupp hPmean
    haveI : IsProbabilityMeasure P := hPprob
    -- a.e. membership in the interval
    have hcompl : P (Set.Icc zl zu)ᶜ = 0 := by
      rw [measure_compl measurableSet_Icc (by simp [hPsupp]), hPsupp, measure_univ]
      simp
    have hae : ∀ᵐ z ∂P, z ∈ Set.Icc zl zu := by
      rw [ae_iff]
      have hset : {z : ℝ | ¬ z ∈ Set.Icc zl zu} = (Set.Icc zl zu)ᶜ := rfl
      rw [hset]
      exact hcompl
    -- integrability of the identity and of the absolute deviation
    have hint_id : Integrable (fun z : ℝ => z) P := by
      refine Integrable.of_bound (by fun_prop) (max |zl| |zu|) ?_
      filter_upwards [hae] with z hz
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · linarith [hz.1, (abs_le.mp (le_max_left |zl| |zu|)).1, (abs_le.mp (le_max_left |zl| |zu|)).2,
          abs_nonneg zl]
      · linarith [hz.2, (abs_le.mp (le_max_right |zl| |zu|)).1, (abs_le.mp (le_max_right |zl| |zu|)).2,
          abs_nonneg zu]
    have hint_abs : Integrable (fun z : ℝ => |z - μ|) P := by
      refine Integrable.of_bound (by fun_prop) (zu - zl) ?_
      filter_upwards [hae] with z hz
      rw [Real.norm_eq_abs, abs_abs, abs_le]
      constructor <;> linarith [hz.1, hz.2, hμ.1, hμ.2]
    -- the chord inequality
    have hchord : ∀ z ∈ Set.Icc zl zu,
        |z - μ| ≤ (zu - μ) * (z - zl) / (zu - zl) + (μ - zl) * (zu - z) / (zu - zl) := by
      intro z hz
      have hsum : (zu - μ) * (z - zl) / (zu - zl) + (μ - zl) * (zu - z) / (zu - zl)
          = ((zu - μ) * (z - zl) + (μ - zl) * (zu - z)) / (zu - zl) := (add_div _ _ _).symm
      rcases le_total z μ with hzμ | hzμ
      · rw [abs_of_nonpos (by linarith), hsum, le_div_iff₀ hd]
        nlinarith [hz.1, hz.2, hμ.1, hμ.2]
      · rw [abs_of_nonneg (by linarith), hsum, le_div_iff₀ hd]
        nlinarith [hz.1, hz.2, hμ.1, hμ.2]
    have hchord_ae : ∀ᵐ z ∂P,
        |z - μ| ≤ (zu - μ) * (z - zl) / (zu - zl) + (μ - zl) * (zu - z) / (zu - zl) :=
      hae.mono hchord
    have hF1 : Integrable (fun z : ℝ => (zu - μ) * (z - zl) / (zu - zl)) P :=
      ((hint_id.sub (integrable_const zl)).const_mul (zu - μ)).div_const (zu - zl)
    have hF2 : Integrable (fun z : ℝ => (μ - zl) * (zu - z) / (zu - zl)) P :=
      (((integrable_const zu).sub hint_id).const_mul (μ - zl)).div_const (zu - zl)
    have hmono := integral_mono_ae hint_abs (hF1.add hF2) hchord_ae
    have h1 : ∫ z : ℝ, (zu - μ) * (z - zl) / (zu - zl) ∂P = (zu - μ) * (μ - zl) / (zu - zl) := by
      rw [integral_div, integral_const_mul, integral_sub hint_id (integrable_const zl), hPmean]
      simp
    have h2 : ∫ z : ℝ, (μ - zl) * (zu - z) / (zu - zl) ∂P = (μ - zl) * (zu - μ) / (zu - zl) := by
      rw [integral_div, integral_const_mul, integral_sub (integrable_const zu) hint_id, hPmean]
      simp
    have hmono' : ∫ z : ℝ, |z - μ| ∂P ≤
        ∫ z : ℝ, ((zu - μ) * (z - zl) / (zu - zl) + (μ - zl) * (zu - z) / (zu - zl)) ∂P := by
      simpa only [Pi.add_apply] using hmono
    rw [integral_add hF1 hF2, h1, h2] at hmono'
    refine le_trans hmono' (le_of_eq ?_)
    field_simp
    ring
  · -- the two-point witness
    set a : ℝ := (zu - μ) / (zu - zl) with ha
    set b : ℝ := (μ - zl) / (zu - zl) with hb
    have ha0 : 0 ≤ a := by
      rw [ha]; exact div_nonneg (by linarith [hμ.2]) hd.le
    have hb0 : 0 ≤ b := by
      rw [hb]; exact div_nonneg (by linarith [hμ.1]) hd.le
    have hab : a + b = 1 := by
      rw [ha, hb]
      field_simp
      ring
    set P : Measure ℝ := ENNReal.ofReal a • Measure.dirac zl + ENNReal.ofReal b • Measure.dirac zu with hP
    have hPuniv : P Set.univ = 1 := by
      rw [hP, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
      simp only [Measure.dirac_apply_of_mem (Set.mem_univ zl),
        Measure.dirac_apply_of_mem (Set.mem_univ zu), smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_add ha0 hb0, hab, ENNReal.ofReal_one]
    have hPI : P (Set.Icc zl zu) = 1 := by
      rw [hP, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
      simp only [Measure.dirac_apply_of_mem (Set.left_mem_Icc.mpr hlt.le),
        Measure.dirac_apply_of_mem (Set.right_mem_Icc.mpr hlt.le), smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_add ha0 hb0, hab, ENNReal.ofReal_one]
    -- integrability with respect to the two Dirac measures
    have hint_dl : Integrable (fun z : ℝ => z) (ENNReal.ofReal a • Measure.dirac zl) :=
      (integrable_dirac (f := fun z : ℝ => z) (a := zl) (by simp)).smul_measure
        ENNReal.ofReal_ne_top
    have hint_du : Integrable (fun z : ℝ => z) (ENNReal.ofReal b • Measure.dirac zu) :=
      (integrable_dirac (f := fun z : ℝ => z) (a := zu) (by simp)).smul_measure
        ENNReal.ofReal_ne_top
    have hint_abs_l : Integrable (fun z : ℝ => |z - μ|) (ENNReal.ofReal a • Measure.dirac zl) :=
      (integrable_dirac (f := fun z : ℝ => |z - μ|) (a := zl) (by simp)).smul_measure
        ENNReal.ofReal_ne_top
    have hint_abs_u : Integrable (fun z : ℝ => |z - μ|) (ENNReal.ofReal b • Measure.dirac zu) :=
      (integrable_dirac (f := fun z : ℝ => |z - μ|) (a := zu) (by simp)).smul_measure
        ENNReal.ofReal_ne_top
    have hmean : ∫ z : ℝ, z ∂P = μ := by
      rw [hP, integral_add_measure hint_dl hint_du, integral_smul_measure, integral_smul_measure,
        integral_dirac, integral_dirac]
      simp only [ENNReal.toReal_ofReal ha0, ENNReal.toReal_ofReal hb0, smul_eq_mul]
      rw [ha, hb]
      field_simp
      ring
    have hmad : ∫ z : ℝ, |z - μ| ∂P = 2 * (zu - μ) * (μ - zl) / (zu - zl) := by
      rw [hP, integral_add_measure hint_abs_l hint_abs_u, integral_smul_measure,
        integral_smul_measure, integral_dirac, integral_dirac]
      simp only [ENNReal.toReal_ofReal ha0, ENNReal.toReal_ofReal hb0, smul_eq_mul]
      have hzl : |zl - μ| = μ - zl := by
        rw [abs_of_nonpos (sub_nonpos.mpr hμ.1)]; ring
      have hzu : |zu - μ| = zu - μ := by
        rw [abs_of_nonneg (sub_nonneg.mpr hμ.2)]
      rw [hzl, hzu, ha, hb]
      field_simp
      ring
    exact ⟨P, isProbabilityMeasure_iff.mpr hPuniv, hPI, hmean, hmad⟩

-- Prove2me | solution 1 for SOSInference.Means.limit_identity_l2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T06:16:08.130406+00:00
-- url     : https://prove2.me/submissions/ab517734-46e4-4989-acf8-25ae714e4265

import Mathlib
import Definitions.Def_SOSInference_Means_tauLaw
import Theorems.Thm_SOSInference_Means_eq_31

open SOSInference.Means
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace SOSL2Aux

variable {l : ℕ} (M : Model l) (hM : M.Standing)

include hM in
lemma lawX_prob : IsProbabilityMeasure (lawX M) := by
  constructor
  simp only [lawX, lawOfDensity]
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hM.lintegral_fX]

include hM in
lemma Lam_pos (x : E l) : 0 < Lam M x 0 := by
  unfold Lam
  have h1 := hM.fX_pos (x + (1 / 2 : ℝ) • (0 : E l))
  have h2 := hM.fY_pos (x + (1 / 2 : ℝ) • (0 : E l))
  have h3 := hM.kappa_nonneg
  have hG : 0 < Real.Gamma ((l : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hpi : 0 < Real.pi ^ ((l : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have : 0 < M.fX (x + (1 / 2 : ℝ) • (0 : E l)) + M.κ * M.fY (x + (1 / 2 : ℝ) • (0 : E l)) := by
    nlinarith
  positivity

include hM in
lemma Lam_meas : Measurable (fun x => Lam M x 0) := by
  unfold Lam
  have h1 : Measurable (fun x : E l => M.fX (x + (1 / 2 : ℝ) • (0 : E l))) :=
    hM.measurable_fX.comp (measurable_id.add_const _)
  have h2 : Measurable (fun x : E l => M.fY (x + (1 / 2 : ℝ) • (0 : E l))) :=
    hM.measurable_fY.comp (measurable_id.add_const _)
  exact ((h1.add (h2.const_mul _)).mul_const _).div_const _

lemma expMeasure_meas {f : E l → ℝ} (hf : Measurable f) :
    Measurable (fun x => expMeasure (f x)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [expMeasure, gammaMeasure]
  simp_rw [withDensity_apply _ hs]
  have : Measurable (fun p : E l × ℝ => gammaPDF 1 (f p.1) p.2) := by
    unfold gammaPDF gammaPDFReal
    apply Measurable.ennreal_ofReal
    apply Measurable.ite (measurableSet_le measurable_const measurable_snd)
    · fun_prop
    · exact measurable_const
  exact this.lintegral_prod_right'

include hM in
lemma tau_prob : IsProbabilityMeasure (tauLaw M 0) := by
  haveI := lawX_prob M hM
  constructor
  unfold tauLaw
  rw [Measure.bind_apply MeasurableSet.univ (expMeasure_meas (Lam_meas M hM)).aemeasurable]
  have h1 : ∀ x, expMeasure (Lam M x 0) Set.univ = 1 := fun x =>
    (isProbabilityMeasure_expMeasure (Lam_pos M hM x)).measure_univ
  simp [h1]

include hM in
lemma tau_nonneg : ∀ᵐ t ∂(tauLaw M 0), 0 ≤ t := by
  rw [ae_iff]
  have hset : {t : ℝ | ¬ 0 ≤ t} = Set.Iio 0 := by ext t; simp
  rw [hset]
  unfold tauLaw
  rw [Measure.bind_apply measurableSet_Iio (expMeasure_meas (Lam_meas M hM)).aemeasurable]
  have h0 : ∀ x, expMeasure (Lam M x 0) (Set.Iio 0) = 0 := by
    intro x
    simp only [expMeasure, gammaMeasure]
    rw [withDensity_apply _ measurableSet_Iio]
    exact lintegral_gammaPDF_of_nonpos le_rfl
  simp [h0]

end SOSL2Aux

open SOSL2Aux in
theorem solution (M : Model 2) (hM : M.Standing) (z : E 2) (hz : z ≠ 0) :
    (∀ ζ : E 2, ‖ζ‖ ^ 2 * etatilde M ζ = ∫ t, max (‖ζ‖ ^ 2 - t) 0 ∂(tauLaw M 0)) ∧
    IsGreatest (Set.range fun ζ : E 2 => -2 * ⟪ζ, z⟫ - ‖ζ‖ ^ 2 * etatilde M ζ) (phi2 M z) ∧
    -2 * ⟪-(rho M z) • z, z⟫ - ‖-(rho M z) • z‖ ^ 2 * etatilde M (-(rho M z) • z) =
      phi2 M z := by
  haveI := tau_prob M hM
  have hnn := tau_nonneg M hM
  set τ := tauLaw M 0 with hτ
  have hInt : ∀ s : ℝ, Integrable (fun t => max (s - t) 0) τ := by
    intro s
    refine Integrable.of_bound (by fun_prop) (max s 0) ?_
    filter_upwards [hnn] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le_max (by linarith) le_rfl
  -- part 1
  have part1 : ∀ ζ : E 2, ‖ζ‖ ^ 2 * etatilde M ζ = ∫ t, max (‖ζ‖ ^ 2 - t) 0 ∂τ := by
    intro ζ
    unfold etatilde
    by_cases hζ : ζ = 0
    · subst hζ
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
        zero_sub]
      symm
      apply integral_eq_zero_of_ae
      filter_upwards [hnn] with t ht
      simp only [Pi.zero_apply]
      exact max_eq_right (by linarith)
    · have hs : 0 < ‖ζ‖ ^ 2 := by have := norm_pos_iff.mpr hζ; positivity
      rw [← integral_const_mul]
      congr 1; ext t
      rw [mul_max_of_nonneg _ _ hs.le, mul_zero]
      congr 1; field_simp
  -- subgradient inequality
  have subgrad : ∀ a b : ℝ,
      (∫ t, max (b - t) 0 ∂τ) + (a - b) * (τ (Set.Iic b)).toReal ≤ ∫ t, max (a - t) 0 ∂τ := by
    intro a b
    have h : ∀ t, max (b - t) 0 + (a - b) * (Set.Iic b).indicator 1 t ≤ max (a - t) 0 := by
      intro t
      by_cases htb : t ≤ b
      · rw [Set.indicator_of_mem (show t ∈ Set.Iic b from htb)]
        simp only [Pi.one_apply, mul_one]
        rw [max_eq_left (by linarith : (0 : ℝ) ≤ b - t)]
        exact le_trans (by linarith) (le_max_left _ _)
      · rw [Set.indicator_of_notMem (show t ∉ Set.Iic b from htb)]
        simp only [mul_zero, add_zero]
        rw [max_eq_right (by push_neg at htb; linarith : b - t ≤ 0)]
        exact le_max_right _ _
    have hind : Integrable (fun t => (a - b) * (Set.Iic b).indicator (1 : ℝ → ℝ) t) τ :=
      ((integrable_const (1 : ℝ)).indicator measurableSet_Iic).const_mul (a - b)
    have := integral_mono ((hInt b).add hind) (hInt a) h
    simp only [Pi.add_apply] at this
    rw [integral_add (hInt b) hind, integral_const_mul,
      integral_indicator_one measurableSet_Iic, measureReal_def] at this
    exact this
  -- (31)
  obtain ⟨-, hρpos, hρeq⟩ := eq_31 M hM z hz
  set ρ := rho M z with hρ
  set N := ‖z‖ with hN
  have hg : (τ (Set.Iic (ρ ^ 2 * N ^ 2))).toReal = 1 / ρ := by
    rw [hρeq]; unfold gtilde
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hρz : ‖ρ • z‖ ^ 2 = ρ ^ 2 * N ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  -- part 3
  have part3 : -2 * ⟪-ρ • z, z⟫ - ‖-ρ • z‖ ^ 2 * etatilde M (-ρ • z) = phi2 M z := by
    have hη : etatilde M (-ρ • z) = etatilde M (ρ • z) := by
      unfold etatilde; rw [neg_smul, norm_neg]
    unfold phi2
    rw [hη, neg_smul, norm_neg, hρz, inner_neg_left, inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [conj_trivial]
    ring
  have hphi : phi2 M z = 2 * ρ * N ^ 2 - ∫ t, max (ρ ^ 2 * N ^ 2 - t) 0 ∂τ := by
    rw [← part3, neg_smul, norm_neg, ← hρz, ← part1 (ρ • z)]
    have hη : etatilde M (-(ρ • z)) = etatilde M (ρ • z) := by
      unfold etatilde; rw [norm_neg]
    rw [hη, inner_neg_left, inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [conj_trivial]
    ring
  refine ⟨part1, ⟨⟨_, part3⟩, ?_⟩, part3⟩
  rintro _ ⟨ζ, rfl⟩
  simp only
  rw [part1 ζ, hphi]
  set r := ‖ζ‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hin : -2 * ⟪ζ, z⟫ ≤ 2 * r * N := by
    have := abs_real_inner_le_norm ζ z
    have := neg_abs_le ⟪ζ, z⟫
    nlinarith
  have hsg := subgrad (r ^ 2) (ρ ^ 2 * N ^ 2)
  rw [hg] at hsg
  have key : 2 * r * N - (r ^ 2 - ρ ^ 2 * N ^ 2) * (1 / ρ) ≤ 2 * ρ * N ^ 2 := by
    have hsq := sq_nonneg (r - ρ * N)
    rw [mul_one_div, sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hρpos]
    nlinarith
  linarith

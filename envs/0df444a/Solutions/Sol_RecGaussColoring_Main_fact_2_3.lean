-- Prove2me | solution 1 for RecGaussColoring.Main.fact_2_3
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T15:08:09.243623+00:00
-- url     : https://prove2.me/submissions/199a17e6-fad3-49f3-9ddb-50a9aa82d5a0

import Definitions.Def_RecGaussColoring_Main_Gaussian

open MeasureTheory ProbabilityTheory Set Real Filter Topology

theorem mills_aux (x : ℝ) (hx : 0 < x) :
    x / (1 + x ^ 2) * gaussianPDFReal 0 1 x ≤ (gaussianReal 0 1).real (Set.Ici x) ∧
      (gaussianReal 0 1).real (Set.Ici x) ≤ gaussianPDFReal 0 1 x / x := by
  set c : ℝ := (Real.sqrt (2 * π))⁻¹ with hc
  have hc0 : 0 < c := by positivity
  set φ : ℝ → ℝ := fun t => c * Real.exp (-t ^ 2 / 2) with hφ
  have hpdf : gaussianPDFReal 0 1 = φ := by
    funext t; simp [gaussianPDFReal, hφ, hc]
  have hreal : (gaussianReal 0 1).real (Set.Ici x) = ∫ t in Ioi x, φ t := by
    rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero, ENNReal.toReal_ofReal
      (setIntegral_nonneg measurableSet_Ici (fun t _ => gaussianPDFReal_nonneg _ _ _)),
      integral_Ici_eq_integral_Ioi, hpdf]
  rw [hreal, hpdf]
  have hφint : Integrable φ := by
    have := (integrable_gaussianPDFReal 0 1); rwa [hpdf] at this
  have hexp_tend : Tendsto (fun t : ℝ => Real.exp (-t ^ 2 / 2)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    apply Tendsto.atBot_div_const two_pos
    exact tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero)
  constructor
  · -- lower bound
    set H : ℝ → ℝ := fun t => c * (t / (1 + t ^ 2)) * Real.exp (-t ^ 2 / 2) with hH
    set D : ℝ → ℝ := fun t => -(φ t * ((t ^ 4 + 2 * t ^ 2 - 1) / (1 + t ^ 2) ^ 2)) with hD
    have hderiv : ∀ t ∈ Ioi x, HasDerivAt H (D t) t := by
      intro t _
      have h1 : HasDerivAt (fun t : ℝ => t / (1 + t ^ 2))
          ((1 * (1 + t ^ 2) - t * (2 * t)) / (1 + t ^ 2) ^ 2) t := by
        apply HasDerivAt.div (hasDerivAt_id t)
        · simpa using ((hasDerivAt_pow 2 t).const_add 1)
        · positivity
      have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t ^ 2 / 2))
          (Real.exp (-t ^ 2 / 2) * (-(2 * t) / 2)) t := by
        have := ((hasDerivAt_pow 2 t).neg.div_const 2).exp
        simpa using this
      have key := (h1.const_mul c).mul h2
      refine key.congr_deriv ?_
      simp only [D, φ]
      have : (1 + t ^ 2) ≠ 0 := by positivity
      field_simp
      ring
    have hratio : ∀ t : ℝ, |(t ^ 4 + 2 * t ^ 2 - 1) / (1 + t ^ 2) ^ 2| ≤ 1 := by
      intro t
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (1 + t ^ 2) ^ 2), div_le_one (by positivity),
        abs_le]
      constructor <;> nlinarith [sq_nonneg t, sq_nonneg (t ^ 2)]
    have hDint : IntegrableOn D (Ioi x) := by
      refine (Integrable.mono' hφint.integrableOn ?_ ?_)
      · apply Continuous.aestronglyMeasurable
        simp only [D, φ]
        apply Continuous.neg
        apply Continuous.mul (by fun_prop)
        apply Continuous.div (by fun_prop) (by fun_prop)
        intro t; positivity
      · filter_upwards with t
        simp only [hD, norm_neg, norm_mul, Real.norm_eq_abs]
        have hp : 0 ≤ φ t := by simp only [φ]; positivity
        rw [abs_of_nonneg hp]
        calc φ t * |(t ^ 4 + 2 * t ^ 2 - 1) / (1 + t ^ 2) ^ 2| ≤ φ t * 1 :=
              mul_le_mul_of_nonneg_left (hratio t) hp
          _ = φ t := mul_one _
    have hHtend : Tendsto H atTop (𝓝 0) := by
      have hb : Tendsto (fun t : ℝ => t / (1 + t ^ 2)) atTop (𝓝 0) := by
        have : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
        apply squeeze_zero' _ _ this
        · filter_upwards [eventually_gt_atTop 0] with t ht; positivity
        · filter_upwards [eventually_gt_atTop 0] with t ht
          rw [div_le_iff₀ (by positivity)]
          field_simp
          nlinarith
      have := (hb.const_mul c).mul hexp_tend
      simpa [hH] using this
    have hcont : ContinuousWithinAt H (Ici x) x := by
      apply Continuous.continuousWithinAt
      simp only [hH]
      apply Continuous.mul _ (by fun_prop)
      apply Continuous.mul continuous_const
      apply Continuous.div (by fun_prop) (by fun_prop)
      intro t; positivity
    have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hDint hHtend
    have hle : ∫ t in Ioi x, -D t ≤ ∫ t in Ioi x, φ t := by
      apply setIntegral_mono_on hDint.neg hφint.integrableOn measurableSet_Ioi
      intro t _
      simp only [D, φ, Pi.neg_apply, neg_neg]
      have hp : 0 ≤ φ t := by simp only [φ]; positivity
      have := (abs_le.mp (hratio t)).2
      nlinarith
    rw [integral_neg, hFTC] at hle
    simp only [hH, zero_sub, neg_neg] at hle
    calc x / (1 + x ^ 2) * φ x = c * (x / (1 + x ^ 2)) * Real.exp (-x ^ 2 / 2) := by
          simp only [φ]; ring
      _ ≤ _ := hle
  · -- upper bound
    set F : ℝ → ℝ := fun t => -(c * Real.exp (-t ^ 2 / 2)) with hF
    have hderiv : ∀ t ∈ Ioi x, HasDerivAt F (t * φ t) t := by
      intro t _
      have key := (((hasDerivAt_pow 2 t).neg.div_const 2).exp.const_mul c).neg
      refine key.congr_deriv ?_
      simp only [φ, Pi.neg_apply]
      push_cast
      ring
    have hint : IntegrableOn (fun t => t * φ t) (Ioi x) := by
      have := (integrable_mul_exp_neg_mul_sq (b := (1/2:ℝ)) (by norm_num)).const_mul c
      refine (this.congr (Eventually.of_forall (fun t => ?_))).integrableOn
      simp only [φ]; ring_nf
    have hFtend : Tendsto F atTop (𝓝 0) := by
      have := (hexp_tend.const_mul c).neg
      simpa [hF] using this
    have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto (Continuous.continuousWithinAt
      (by simp only [hF]; fun_prop)) hderiv hint hFtend
    have hle : ∫ t in Ioi x, φ t ≤ ∫ t in Ioi x, t * φ t / x := by
      apply setIntegral_mono_on hφint.integrableOn (hint.div_const x) measurableSet_Ioi
      intro t ht
      have ht : x < t := ht
      have hp : 0 ≤ φ t := by simp only [φ]; positivity
      rw [le_div_iff₀ hx]
      nlinarith
    rw [integral_div, hFTC] at hle
    simpa [hF, hφ] using hle


theorem solution (t : ℝ) (ht : 0 < t) :
  t/(1+t^2) * (1/Real.sqrt (2*Real.pi)) * Real.exp (-t^2/2) ≤ RecGaussColoring.Main.PhiTail t ∧
    RecGaussColoring.Main.PhiTail t ≤ Real.exp (-t^2/2) := by
  haveI : NullSingletonClass (gaussianReal 0 1) :=
    ⟨fun x => (gaussianReal_absolutelyContinuous 0 one_ne_zero) (Real.volume_singleton)⟩
  have htail : RecGaussColoring.Main.PhiTail t = (gaussianReal 0 1).real (Set.Ici t) := by
    rw [RecGaussColoring.Main.PhiTail, Cohen2019.Robust.Phi, cdf_eq_real,
      ← probReal_compl_eq_one_sub measurableSet_Iic, Set.compl_Iic, measureReal_def, measureReal_def,
      measure_congr Ioi_ae_eq_Ici]
  rw [htail]
  constructor
  · have hpdf : gaussianPDFReal 0 1 t = 1 / Real.sqrt (2 * Real.pi) * Real.exp (-t ^ 2 / 2) := by
      simp [gaussianPDFReal]
    have h := (mills_aux t ht).1
    rw [hpdf] at h
    calc t / (1 + t ^ 2) * (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-t ^ 2 / 2)
        = t / (1 + t ^ 2) * (1 / Real.sqrt (2 * Real.pi) * Real.exp (-t ^ 2 / 2)) := by ring
      _ ≤ _ := h
  · have h := measure_ge_le_exp_mul_mgf (X := id) (μ := gaussianReal 0 1) t ht.le
      (integrable_exp_mul_gaussianReal t)
    rw [mgf_id_gaussianReal, ← Real.exp_add] at h
    have e : -t * t + ((0 : ℝ) * t + ((1 : NNReal) : ℝ) * t ^ 2 / 2) = -t ^ 2 / 2 := by push_cast; ring
    rw [e] at h
    exact h

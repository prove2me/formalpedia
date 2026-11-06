-- Prove2me | solution 1 for ProductFraming.Nest.exponential_ratio_eq_pi_sq_div_six
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T07:03:57.366438+00:00
-- url     : https://prove2.me/submissions/48e833e6-d53e-4167-ab3b-6be91d3421df

import Mathlib

open MeasureTheory ProbabilityTheory Set Real

namespace PFNExpAux

lemma integral_expMeasure {r : ℝ} (hr : 0 < r) (f : ℝ → ℝ) :
    ∫ x, f x ∂(expMeasure r) = ∫ x in Ioi 0, r * exp (-(r * x)) * f x := by
  show ∫ x, f x ∂(volume.withDensity (fun x => ENNReal.ofReal (gammaPDFReal 1 r x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
      ((measurable_gammaPDFReal 1 r).ennreal_ofReal)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  rw [← integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici]
  congr 1
  ext x
  simp only [smul_eq_mul, indicator]
  rw [ENNReal.toReal_ofReal (gammaPDFReal_nonneg one_pos hr x)]
  unfold gammaPDFReal
  split_ifs with h1 h2 h2
  · simp
  · exact absurd (mem_Ici.mpr h1) h2
  · exact absurd (mem_Ici.mp h2) h1
  · simp

lemma ae_nonneg_expMeasure (r : ℝ) : ∀ᵐ w ∂(expMeasure r), 0 ≤ w := by
  rw [ae_iff]
  simp only [not_le]
  show expMeasure r (Iio 0) = 0
  rw [expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Iio]
  rw [setLIntegral_congr_fun measurableSet_Iio (g := fun _ => 0) (fun x hx => gammaPDF_of_neg hx)]
  simp

/-- `E[min(Z, w)] = (1 - e^{-r w}) / r` for `Z` exponential with rate `r` and `w ≥ 0`. -/
lemma integral_min_expMeasure {r : ℝ} (hr : 0 < r) {w : ℝ} (hw : 0 ≤ w) :
    ∫ z, min z w ∂(expMeasure r) = (1 - exp (-(r * w))) / r := by
  rw [integral_expMeasure hr]
  have hint1 : IntegrableOn (fun z => r * exp (-(r * z)) * min z w) (Ioc 0 w) := by
    apply ContinuousOn.integrableOn_Icc ?_ |>.mono_set Ioc_subset_Icc_self
    fun_prop
  have hint2 : IntegrableOn (fun z => r * exp (-(r * z)) * min z w) (Ioi w) := by
    have : IntegrableOn (fun z => r * w * exp (-r * z)) (Ioi w) :=
      (exp_neg_integrableOn_Ioi w hr).const_mul (r * w)
    refine this.congr_fun (fun z hz => ?_) measurableSet_Ioi
    simp only
    rw [min_eq_right (le_of_lt (mem_Ioi.mp hz))]
    ring_nf
  rw [← Ioc_union_Ioi_eq_Ioi hw, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    hint1 hint2]
  have h1 : ∫ z in Ioc 0 w, r * exp (-(r * z)) * min z w
      = ∫ z in Ioc 0 w, r * z * exp (-(r * z)) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro z hz
    simp only
    rw [min_eq_left hz.2]; ring
  have h2 : ∫ z in Ioi w, r * exp (-(r * z)) * min z w
      = ∫ z in Ioi w, (r * w) * exp ((-r) * z) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    simp only
    rw [min_eq_right (le_of_lt (mem_Ioi.mp hz))]; ring_nf
  rw [h1, h2, integral_const_mul, integral_exp_mul_Ioi (by linarith)]
  rw [← intervalIntegral.integral_of_le hw]
  have hderiv : ∀ x ∈ uIcc 0 w, HasDerivAt (fun z => -z * exp (-(r * z)) - exp (-(r * z)) / r)
      (r * x * exp (-(r * x))) x := by
    intro x _
    have he : HasDerivAt (fun z => exp (-(r * z))) (exp (-(r * x)) * (-r)) x := by
      have := ((hasDerivAt_id x).const_mul r).neg.exp
      simpa using this
    have := ((hasDerivAt_neg x).mul he).sub (he.div_const r)
    have h' := this.congr_deriv (show _ = r * x * exp (-(r * x)) by field_simp; ring)
    exact h'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; fun_prop)]
  field_simp
  ring_nf
  rw [Real.exp_zero]; ring

end PFNExpAux

namespace PFNZetaAux

lemma integral_term (k : ℕ) :
    ∫ u in Ioi (0 : ℝ), u * exp (-(((k : ℝ) + 1) * u)) = 1 / ((k : ℝ) + 1) ^ 2 := by
  have hr : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) hr
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.Gamma_two, mul_one] at h
  simp only [Real.rpow_one] at h
  rw [h]
  norm_num [Real.rpow_two, div_pow]

lemma integrable_term (k : ℕ) :
    IntegrableOn (fun u : ℝ => u * exp (-(((k : ℝ) + 1) * u))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_term]
  positivity

lemma hasSum_term {u : ℝ} (hu : 0 < u) :
    HasSum (fun k : ℕ => u * exp (-(((k : ℝ) + 1) * u))) (u * exp (-u) / (1 - exp (-u))) := by
  have h0 : 0 ≤ exp (-u) := (exp_pos _).le
  have h1 : exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hg := (hasSum_geometric_of_lt_one h0 h1).mul_left (u * exp (-u))
  have hf : (fun k : ℕ => u * exp (-(((k : ℝ) + 1) * u))) = fun i => u * exp (-u) * exp (-u) ^ i := by
    funext k
    rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    congr 2; ring
  rw [hf, div_eq_mul_inv]
  exact hg

lemma hasSum_inv_sq : HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simp only [Finset.sum_range_one, Nat.cast_zero] at h
  norm_num at h
  simpa [one_div] using h

lemma integral_eq_zeta_two :
    ∫ u in Ioi (0 : ℝ), u * exp (-u) / (1 - exp (-u)) = Real.pi ^ 2 / 6 := by
  have hint : ∀ k : ℕ, Integrable (fun u : ℝ => u * exp (-(((k : ℝ) + 1) * u)))
      (volume.restrict (Ioi 0)) := integrable_term
  have hnorm : ∀ k : ℕ, ∫ u in Ioi (0 : ℝ), ‖u * exp (-(((k : ℝ) + 1) * u))‖
      = 1 / ((k : ℝ) + 1) ^ 2 := by
    intro k
    rw [← integral_term k]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    simp only
    rw [Real.norm_of_nonneg (mul_nonneg (le_of_lt hu) (exp_pos _).le)]
  have hsum : Summable fun k : ℕ => ∫ u in Ioi (0 : ℝ), ‖u * exp (-(((k : ℝ) + 1) * u))‖ := by
    simp_rw [hnorm]; exact hasSum_inv_sq.summable
  have H := hasSum_integral_of_summable_integral_norm hint hsum
  simp_rw [integral_term] at H
  rw [hasSum_inv_sq.unique H]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  exact ((hasSum_term hu).tsum_eq).symm

end PFNZetaAux

open PFNExpAux PFNZetaAux in
theorem solution (μ : ℝ) (hμ : 0 < μ) :
    ∫ w, w / (μ * (1 - Real.exp (-w / μ))) ∂(expMeasure μ⁻¹) = Real.pi ^ 2 / 6 := by
  rw [integral_expMeasure (inv_pos.mpr hμ)]
  have hsub := integral_comp_mul_left_Ioi
    (fun w => μ⁻¹ * exp (-(μ⁻¹ * w)) * (w / (μ * (1 - exp (-w / μ))))) 0 hμ
  simp only [mul_zero, smul_eq_mul] at hsub
  have : ∫ x in Ioi (0 : ℝ), μ⁻¹ * exp (-(μ⁻¹ * x)) * (x / (μ * (1 - exp (-x / μ))))
      = μ * ∫ x in Ioi (0 : ℝ), μ⁻¹ * exp (-(μ⁻¹ * (μ * x))) * (μ * x / (μ * (1 - exp (-(μ * x) / μ)))) := by
    rw [hsub, ← mul_assoc, mul_inv_cancel₀ hμ.ne', one_mul]
  rw [this, ← integral_eq_zeta_two, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  simp only
  have h1 : μ⁻¹ * (μ * u) = u := by field_simp
  have h2 : -(μ * u) / μ = -u := by field_simp
  rw [h1, h2]
  field_simp

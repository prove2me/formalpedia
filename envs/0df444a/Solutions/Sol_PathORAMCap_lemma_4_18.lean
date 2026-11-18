-- Prove2me | solution 1 for PathORAMCap.lemma_4_18
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T05:51:35.800641+00:00
-- url     : https://prove2.me/submissions/930de1ab-63b4-4f1a-bf72-98749d00b8d1

import Mathlib

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

lemma factor (k : ℕ) :
    ∫⁻ x : ℝ, poissonMeasure x.toNNReal {k} ∂(expMeasure 1) = ((2 : ℝ≥0∞) ^ (k + 1))⁻¹ := by
  have hpm : Measurable (fun x : ℝ => poissonMeasure x.toNNReal {k}) := by
    simp_rw [poissonMeasure_singleton]; fun_prop
  rw [expMeasure, gammaMeasure, lintegral_withDensity_eq_lintegral_mul₀ (f := gammaPDF 1 1)
    (measurable_gammaPDFReal 1 1).ennreal_ofReal.aemeasurable hpm.aemeasurable]
  have hpt : ∀ x : ℝ, (gammaPDF 1 1 * fun x : ℝ => poissonMeasure x.toNNReal {k}) x =
      (Ioi (0:ℝ)).indicator (fun x => ENNReal.ofReal (x ^ k * Real.exp (-(2 * x)) / k.factorial)) x
      + ({0} : Set ℝ).indicator (fun x => (gammaPDF 1 1 * fun x : ℝ => poissonMeasure x.toNNReal {k}) x) x := by
    intro x
    rcases lt_trichotomy x 0 with h | h | h
    · simp [indicator, h.not_gt, h.ne, gammaPDF_of_neg h]
    · subst h; simp [indicator]
    · simp only [Pi.mul_apply, indicator, mem_Ioi, h, if_true, mem_singleton_iff, h.ne', if_false,
        add_zero, gammaPDF_of_nonneg h.le, poissonMeasure_singleton]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Real.coe_toNNReal _ h.le, Real.Gamma_one, Real.rpow_one, sub_self, Real.rpow_zero]
      rw [show -(2 * x) = -x + -x by ring, Real.exp_add]
      simp only [one_div, div_one, inv_one, one_mul, mul_one]
      ring
  rw [lintegral_congr hpt]
  rw [lintegral_add_left (by
      apply Measurable.indicator _ measurableSet_Ioi
      fun_prop)]
  have h0 : ∫⁻ x : ℝ, ({0} : Set ℝ).indicator
      (fun x => (gammaPDF 1 1 * fun x : ℝ => poissonMeasure x.toNNReal {k}) x) x = 0 := by
    rw [lintegral_indicator (measurableSet_singleton 0)]
    simp
  rw [h0, add_zero, lintegral_indicator measurableSet_Ioi]
  have hI : ∫ x in Ioi (0:ℝ), x ^ k * Real.exp (-(2 * x)) / k.factorial = (1/2) ^ (k+1) := by
    rw [integral_div]
    have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k:ℝ) + 1) (r := 2) (by positivity) two_pos
    simp only [add_sub_cancel_right, Real.rpow_natCast] at this
    rw [this, Real.Gamma_nat_eq_factorial, ← Real.rpow_natCast]
    push_cast
    field_simp
  have hint : IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-(2 * x)) / k.factorial) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero; rw [hI]; positivity
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))]
      (fun x : ℝ => x ^ k * Real.exp (-(2 * x)) / k.factorial) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx : (0:ℝ) < x := hx
    simp only [Pi.zero_apply]; positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, hI]
  rw [one_div, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos two_pos,
    ENNReal.ofReal_ofNat, ENNReal.inv_pow]

theorem solution (V : Type*) [Fintype V] (k : V → ℕ) :
    ∫⁻ lam : V → ℝ, ∏ v, poissonMeasure (lam v).toNNReal {k v}
        ∂(Measure.pi fun _ : V => expMeasure 1) =
      ∏ v, ((2 : ℝ≥0∞) ^ (k v + 1))⁻¹ := by
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  have hmeas : ∀ v, Measurable (fun x : ℝ => poissonMeasure x.toNNReal {k v}) := by
    intro v; simp_rw [poissonMeasure_singleton]; fun_prop
  have hind := iIndepFun_pi (μ := fun _ : V => expMeasure 1)
    (X := fun v x => poissonMeasure x.toNNReal {k v}) (fun v => (hmeas v).aemeasurable)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    (fun v => (hmeas v).comp (measurable_pi_apply v))]
  congr 1; funext v
  rw [← factor (k v)]
  exact (measurePreserving_eval (fun _ : V => expMeasure 1) v).lintegral_comp (hmeas v)

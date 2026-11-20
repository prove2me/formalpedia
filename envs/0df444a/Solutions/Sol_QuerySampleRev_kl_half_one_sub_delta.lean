-- Prove2me | solution 1 for QuerySampleRev.kl_half_one_sub_delta
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T15:43:00.926202+00:00
-- url     : https://prove2.me/submissions/4398be7c-efc7-4316-8aa0-8843f6bd513d

import Mathlib
import Definitions.Def_ExploreFirst_FundIneq_Setting

open MeasureTheory InformationTheory ExploreFirst.FundIneq
open scoped ENNReal

lemma ber_prob' (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) : IsProbabilityMeasure (bernoulliLaw a) := by
  constructor
  simp only [bernoulliLaw, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]; simp

/-- the KL divergence between two Bernoulli laws with `q ∈ (0,1)`, `p ∈ (0,1)` -/
lemma klBer_eq (p q : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    klBer p q = ENNReal.ofReal (p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))) := by
  classical
  haveI := ber_prob' p hp0.le hp1.le
  haveI := ber_prob' q hq0.le hq1.le
  set f : ℝ → ℝ≥0∞ := fun x => if x = 1 then ENNReal.ofReal (p / q) else ENNReal.ofReal ((1 - p) / (1 - q))
    with hf
  have hfm : Measurable f := Measurable.ite (measurableSet_singleton 1) measurable_const measurable_const
  have hwd : (bernoulliLaw q).withDensity f = bernoulliLaw p := by
    ext s hs
    rw [withDensity_apply _ hs, bernoulliLaw, Measure.restrict_add, lintegral_add_measure,
      Measure.restrict_smul, Measure.restrict_smul, lintegral_smul_measure, lintegral_smul_measure]
    simp only [bernoulliLaw, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [restrict_dirac' hs, restrict_dirac' hs]
    have hf1 : f 1 = ENNReal.ofReal (p / q) := by simp [hf]
    have hf0 : f 0 = ENNReal.ofReal ((1 - p) / (1 - q)) := by simp [hf]
    have e1 : ENNReal.ofReal q * ENNReal.ofReal (p / q) = ENNReal.ofReal p := by
      rw [← ENNReal.ofReal_mul hq0.le]; congr 1; field_simp
    have e0 : ENNReal.ofReal (1 - q) * ENNReal.ofReal ((1 - p) / (1 - q)) = ENNReal.ofReal (1 - p) := by
      rw [← ENNReal.ofReal_mul (by linarith)]; congr 1; rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self (by linarith : (1:ℝ) - q ≠ 0), mul_one]
    by_cases h1 : (1 : ℝ) ∈ s <;> by_cases h0 : (0 : ℝ) ∈ s <;>
      simp [h1, h0, Measure.dirac_apply' _ hs, lintegral_dirac, hf1, hf0, e1, e0]
  have hac : bernoulliLaw p ≪ bernoulliLaw q := by
    rw [← hwd]; exact withDensity_absolutelyContinuous _ _
  have hrn : (bernoulliLaw p).rnDeriv (bernoulliLaw q) =ᵐ[bernoulliLaw q] f := by
    rw [← hwd]; exact Measure.rnDeriv_withDensity _ hfm
  have hrnp : (bernoulliLaw p).rnDeriv (bernoulliLaw q) =ᵐ[bernoulliLaw p] f := hac.ae_le hrn
  have hllr : llr (bernoulliLaw p) (bernoulliLaw q) =ᵐ[bernoulliLaw p] fun x => Real.log (f x).toReal := by
    filter_upwards [hrnp] with x hx; simp [llr, hx]
  have hint : Integrable (fun x => Real.log (f x).toReal) (bernoulliLaw p) := by
    rw [bernoulliLaw]
    exact ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top).add_measure
      ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
  rw [klBer, klDiv_of_ac_of_integrable hac (hint.congr hllr.symm), integral_congr_ae hllr,
    probReal_univ, probReal_univ, add_sub_cancel_right]
  congr 1
  rw [bernoulliLaw, integral_add_measure ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
      ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  simp [hf, ENNReal.toReal_ofReal hp0.le, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 1 - p),
    ENNReal.toReal_ofReal (div_nonneg hp0.le hq0.le),
    ENNReal.toReal_ofReal (div_nonneg (by linarith : (0:ℝ) ≤ 1 - p) (by linarith : (0:ℝ) ≤ 1 - q))]


theorem solution {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) :
    ExploreFirst.FundIneq.klBer (1 / 2) (1 - δ) =
        ENNReal.ofReal (1 / 2 * Real.log (1 / (4 * δ * (1 - δ)))) ∧
      ENNReal.ofReal (1 / 16 * Real.log (1 / δ)) ≤ ExploreFirst.FundIneq.klBer (1 / 2) (1 - δ) := by
  have h1d : 0 < 1 - δ := by linarith
  have hval : 1 / 2 * Real.log ((1 / 2) / (1 - δ)) + (1 - 1 / 2) * Real.log ((1 - 1 / 2) / (1 - (1 - δ)))
      = 1 / 2 * Real.log (1 / (4 * δ * (1 - δ))) := by
    have e : (1 / 2 : ℝ) / (1 - δ) * ((1 - 1 / 2) / (1 - (1 - δ))) = 1 / (4 * δ * (1 - δ)) := by
      rw [show (1:ℝ) - (1 - δ) = δ by ring, show (1:ℝ) - 1 / 2 = 1 / 2 by norm_num]
      field_simp; ring
    rw [← e, Real.log_mul (by positivity) (by
      have : (0:ℝ) < (1 - 1 / 2) / (1 - (1 - δ)) := by
        apply div_pos (by norm_num); linarith
      exact this.ne')]
    ring
  have hkl : ExploreFirst.FundIneq.klBer (1 / 2) (1 - δ)
      = ENNReal.ofReal (1 / 2 * Real.log (1 / (4 * δ * (1 - δ)))) := by
    rw [klBer_eq (1 / 2) (1 - δ) (by norm_num) (by norm_num) h1d (by linarith), hval]
  refine ⟨hkl, ?_⟩
  rw [hkl]
  refine ENNReal.ofReal_le_ofReal ?_
  set u := 1 / (4 * δ) with hu
  have hu0 : 0 < u := by positivity
  have hlog1 : Real.log (1 / δ) = Real.log 4 + Real.log u := by
    rw [← Real.log_mul (by norm_num) hu0.ne', hu]; congr 1; field_simp
  have hlog2 : Real.log (1 / (4 * δ * (1 - δ))) = Real.log u - Real.log (1 - δ) := by
    rw [← Real.log_div hu0.ne' h1d.ne', hu]; congr 1; field_simp
  have hlu : 1 - 4 * δ ≤ Real.log u := by
    have := Real.one_sub_inv_le_log_of_pos hu0
    rw [hu, one_div, inv_inv] at this
    rw [hu, one_div]; exact this
  have hl1 : Real.log (1 - δ) ≤ -δ := by
    have := Real.log_le_sub_one_of_pos h1d; linarith
  have hl4 : Real.log 4 < 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast
    have := Real.log_two_lt_d9; linarith
  rw [hlog1, hlog2]
  nlinarith

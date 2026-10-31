-- Prove2me | solution 1 for PoolOrNot.Moderate.eq_22
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T10:24:46.207388+00:00
-- url     : https://prove2.me/submissions/63ac6a5f-2254-47fa-a5dc-0deec80865f1

import Mathlib
import Definitions.Def_PoolOrNot_Moderate_Waiting

open MeasureTheory ProbabilityTheory

namespace PoolOrNotEq22Aux

lemma laplace_exp {r : ℝ} (hr : 0 < r) {s : ℝ} (hs : 0 ≤ s) :
    ∫ x, Real.exp (-s * x) ∂(expMeasure r) = r / (s + r) := by
  unfold expMeasure gammaMeasure
  have hpdf : gammaPDF 1 r = fun x => ENNReal.ofReal (gammaPDFReal 1 r x) := rfl
  rw [hpdf, integral_withDensity_eq_integral_toReal_smul (measurable_gammaPDFReal 1 r).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hsplit : ∀ x : ℝ, (ENNReal.ofReal (gammaPDFReal 1 r x)).toReal • Real.exp (-s * x)
      = Set.indicator (Set.Ici 0) (fun x => r * Real.exp ((-(s + r)) * x)) x := by
    intro x
    rw [ENNReal.toReal_ofReal (gammaPDFReal_nonneg zero_lt_one hr x), smul_eq_mul]
    by_cases hx : 0 ≤ x
    · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hx)]
      simp only [gammaPDFReal, if_pos hx, Real.rpow_one, sub_self, Real.rpow_zero,
        Real.Gamma_one, div_one, mul_one]
      rw [mul_assoc, ← Real.exp_add]; ring_nf
    · rw [Set.indicator_of_notMem (by simpa using hx)]
      simp [gammaPDFReal, hx]
  simp_rw [hsplit]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_const_mul,
    integral_exp_mul_Ioi (by linarith) 0]
  have : s + r ≠ 0 := by linarith
  field_simp
  simp

lemma laplace_conv (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (s : ℝ) :
    ∫ x, Real.exp (-s * x) ∂(Measure.conv μ ν) =
      (∫ x, Real.exp (-s * x) ∂μ) * ∫ x, Real.exp (-s * x) ∂ν := by
  unfold Measure.conv
  rw [integral_map (by fun_prop) (by fun_prop)]
  rw [← integral_prod_mul]
  congr 1; ext z; rw [← Real.exp_add]; ring_nf

lemma hypoLaw_prob (rate : ℕ → ℝ) (hr : ∀ k, 0 < rate k) :
    ∀ k, IsProbabilityMeasure (PoolOrNot.Moderate.hypoLaw rate k)
  | 0 => by simp only [PoolOrNot.Moderate.hypoLaw]; infer_instance
  | k + 1 => by
    simp only [PoolOrNot.Moderate.hypoLaw]
    have := hypoLaw_prob rate hr k
    have := isProbabilityMeasure_expMeasure (hr k)
    unfold Measure.conv
    exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma laplace_hypo (rate : ℕ → ℝ) (hr : ∀ k, 0 < rate k) {s : ℝ} (hs : 0 ≤ s) :
    ∀ k, ∫ x, Real.exp (-s * x) ∂(PoolOrNot.Moderate.hypoLaw rate k) =
      ∏ j ∈ Finset.range k, rate j / (s + rate j)
  | 0 => by simp [PoolOrNot.Moderate.hypoLaw]
  | k + 1 => by
    simp only [PoolOrNot.Moderate.hypoLaw]
    have := hypoLaw_prob rate hr k
    have := isProbabilityMeasure_expMeasure (hr k)
    rw [laplace_conv, laplace_hypo rate hr hs k, laplace_exp (hr k) hs, Finset.prod_range_succ]

end PoolOrNotEq22Aux

open PoolOrNot.Moderate in
theorem solution (μ θ : ℝ) (hμ : 0 < μ) (hθ : 0 < θ) (i : ℕ) (hi : 1 ≤ i) (s : ℝ) (hs : 0 ≤ s) :
    ∫ x, Real.exp (-s * x) ∂(taLaw μ θ i) =
      ∏ k ∈ Finset.range i, (μ + (k : ℝ) * θ) / (s + μ + (k : ℝ) * θ) := by
  unfold taLaw
  rw [PoolOrNotEq22Aux.laplace_hypo _ (fun k => by positivity) hs i]
  refine Finset.prod_congr rfl fun k _ => ?_
  ring_nf

-- Prove2me | solution 1 for QueueingFundamentals.GG1.wiener_hopf_transform
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:50:51.49427+00:00
-- url     : https://prove2.me/submissions/600785bc-bdca-47b1-b2b3-5489b802c021

import Mathlib
import Definitions.Def_QueueingFundamentals_GG1_Lindley



namespace QueueingFundamentals.GG1

open MeasureTheory

lemma qf_diffLaw_prob (A B : Measure ℝ) [IsProbabilityMeasure A] [IsProbabilityMeasure B] :
    IsProbabilityMeasure (diffLaw A B) := by
  unfold diffLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma qf_cdf_mono (ν : Measure ℝ) [IsFiniteMeasure ν] : Monotone (cdfOf ν) := by
  intro a b hab
  unfold cdfOf
  exact measureReal_mono (Set.Iic_subset_Iic.mpr hab)

lemma qf_cdf_meas (ν : Measure ℝ) [IsFiniteMeasure ν] : Measurable (cdfOf ν) :=
  (qf_cdf_mono ν).measurable

lemma qf_cdf_nonneg (ν : Measure ℝ) (t : ℝ) : 0 ≤ cdfOf ν t := by
  unfold cdfOf; exact measureReal_nonneg

lemma qf_cdf_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℝ) : cdfOf ν t ≤ 1 := by
  unfold cdfOf; exact measureReal_le_one

lemma qf_stat_neg {U ν : Measure ℝ} (h : lindleyStep U ν = ν) (t : ℝ) (ht : t < 0) :
    cdfOf ν t = 0 := by
  unfold cdfOf
  rw [← h]
  unfold lindleyStep
  rw [measureReal_def, Measure.map_apply (by fun_prop) measurableSet_Iic]
  have : (fun p : ℝ × ℝ => max 0 (p.1 + p.2)) ⁻¹' Set.Iic t = ∅ := by
    ext p; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_le]
    exact lt_of_lt_of_le ht (le_max_left _ _)
  rw [this]; simp

lemma qf_stat_pos {U ν : Measure ℝ} [IsProbabilityMeasure U] [IsProbabilityMeasure ν]
    (h : lindleyStep U ν = ν) (t : ℝ) (ht : 0 ≤ t) :
    cdfOf ν t = ∫ x, cdfOf ν (t - x) ∂U := by
  have key : ν (Set.Iic t) = ∫⁻ x, ν (Set.Iic (t - x)) ∂U := by
    conv_lhs => rw [← h]
    unfold lindleyStep
    rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
    rw [Measure.prod_apply_symm]
    · congr 1; ext x; congr 1; ext w
      simp only [Set.mem_preimage, Set.mem_Iic, max_le_iff, ht, true_and]
      constructor <;> intro hh <;> linarith
    · exact (measurableSet_Iic).preimage (by fun_prop)
  unfold cdfOf
  rw [measureReal_def, key]
  simp only [measureReal_def]
  refine (integral_toReal ?_ ?_).symm
  · have : Antitone (fun x => ν (Set.Iic (t - x))) := by
      intro a b hab; exact measure_mono (Set.Iic_subset_Iic.mpr (by linarith))
    exact this.measurable.aemeasurable
  · exact Filter.Eventually.of_forall (fun x => measure_lt_top _ _)

lemma qf_full_eq_Iic (ν : Measure ℝ) (U : Measure ℝ) (hneg : ∀ t, t < 0 → cdfOf ν t = 0) (t : ℝ) :
    ∫ x in Set.Iic t, cdfOf ν (t - x) ∂U = ∫ x, cdfOf ν (t - x) ∂U := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  simp only [Set.mem_Iic, not_le] at hx
  exact hneg _ (by linarith)

lemma qf_part1 {U ν : Measure ℝ} [IsProbabilityMeasure U] [IsProbabilityMeasure ν]
    (h : lindleyStep U ν = ν) (t : ℝ) :
    negPart U (cdfOf ν) t + cdfOf ν t = ∫ x in Set.Iic t, cdfOf ν (t - x) ∂U := by
  unfold negPart
  split_ifs with ht
  · rw [qf_stat_neg h t ht]; ring
  · rw [zero_add, qf_full_eq_Iic ν U (qf_stat_neg h) t]
    exact qf_stat_pos h t (not_lt.mp ht)

lemma qf_lap_int (ν : Measure ℝ) [IsProbabilityMeasure ν] (hneg : ∀ t, t < 0 → cdfOf ν t = 0)
    (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * (cdfOf ν t : ℂ)) volume := by
  have hg : Integrable (Set.indicator (Set.Ici (0:ℝ)) (fun t => Real.exp (-s.re * t))) volume := by
    have h1 := exp_neg_integrableOn_Ioi 0 hs
    rw [← integrableOn_Ici_iff_integrableOn_Ioi] at h1
    exact h1.integrable_indicator measurableSet_Ici
  refine Integrable.mono' hg ?_ ?_
  · have := qf_cdf_meas ν
    exact (Measurable.mul (by fun_prop) (by fun_prop)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun t => ?_)
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    have hre : (-s * (t : ℂ)).re = -s.re * t := by simp
    rw [hre]
    by_cases ht : t < 0
    · rw [hneg t ht, abs_zero, mul_zero]
      exact Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
    · rw [Set.indicator_of_mem (by simpa using not_lt.mp ht)]
      rw [abs_of_nonneg (qf_cdf_nonneg ν t)]
      have := qf_cdf_le_one ν t
      have := Real.exp_pos (-s.re * t)
      nlinarith

lemma qf_lifetime_exp_int (B : Measure ℝ) [IsProbabilityMeasure B] (hB : B (Set.Iio 0) = 0)
    (σ : ℝ) (hσ : 0 < σ) : Integrable (fun x => Real.exp (-σ * x)) B := by
  refine Integrable.mono' (integrable_const (1:ℝ)) (by fun_prop) ?_
  have := measure_eq_zero_iff_ae_notMem.mp hB
  filter_upwards [this] with x hx
  simp only [Set.mem_Iio, not_lt] at hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  nlinarith

lemma qf_expU_int (A B : Measure ℝ) [IsProbabilityMeasure A] [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0) (σ : ℝ) (hσ : 0 < σ)
    (hA : Integrable (fun x : ℝ => Real.exp (σ * x)) A) :
    Integrable (fun x => Real.exp (-σ * x)) (diffLaw A B) := by
  unfold diffLaw
  rw [integrable_map_measure (by fun_prop) (by fun_prop)]
  have := (qf_lifetime_exp_int B hB σ hσ).mul_prod hA
  refine this.congr (Filter.Eventually.of_forall (fun p => ?_))
  simp only [Function.comp]
  rw [← Real.exp_add]; congr 1; ring

lemma qf_lst_diff (A B : Measure ℝ) [IsFiniteMeasure A] [IsFiniteMeasure B] (s : ℂ) :
    QueueingFundamentals.MG1.lst (diffLaw A B) s =
      QueueingFundamentals.MG1.lst A (-s) * QueueingFundamentals.MG1.lst B s := by
  unfold QueueingFundamentals.MG1.lst diffLaw
  rw [integral_map (by fun_prop) (by fun_prop)]
  have : ∀ p : ℝ × ℝ, Complex.exp (-(s * ((p.1 - p.2 : ℝ) : ℂ))) =
      Complex.exp (-(s * (p.1 : ℂ))) * Complex.exp (-(-s * (p.2 : ℂ))) := by
    intro p; rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp_rw [this]
  exact (integral_prod_mul (fun x : ℝ => Complex.exp (-(s * (x:ℂ)))) (fun y : ℝ => Complex.exp (-(-s*(y:ℂ))))).trans (mul_comm _ _)

lemma qf_lap_conv (U ν : Measure ℝ) [IsProbabilityMeasure U] [IsProbabilityMeasure ν]
    (hneg : ∀ t, t < 0 → cdfOf ν t = 0) (s : ℂ) (hs : 0 < s.re)
    (hU : Integrable (fun x => Real.exp (-s.re * x)) U) :
    Integrable (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * ((∫ x, cdfOf ν (t - x) ∂U : ℝ) : ℂ)) volume ∧
    twoSidedLaplace (fun t => ∫ x, cdfOf ν (t - x) ∂U) s =
      twoSidedLaplace (cdfOf ν) s * QueueingFundamentals.MG1.lst U s := by
  set h : ℝ → ℂ := fun t => Complex.exp (-s * (t : ℂ)) * (cdfOf ν t : ℂ) with hh
  have hint : Integrable h volume := qf_lap_int ν hneg s hs
  set F : ℝ × ℝ → ℂ := fun p => Complex.exp (-s * (p.2 : ℂ)) * (cdfOf ν (p.2 - p.1) : ℂ) with hF
  have hFeq : ∀ x t : ℝ, F (x, t) = Complex.exp (-s * (x : ℂ)) * h (t - x) := by
    intro x t
    simp only [hF, hh]
    rw [← mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring
  have hmeas : AEStronglyMeasurable F (U.prod volume) := by
    have := qf_cdf_meas ν
    exact (Measurable.mul (by fun_prop) (by fun_prop)).aestronglyMeasurable
  have hFint : Integrable F (U.prod volume) := by
    rw [integrable_prod_iff hmeas]
    constructor
    · refine Filter.Eventually.of_forall (fun x => ?_)
      simp_rw [hFeq]
      exact (hint.comp_sub_right x).const_mul _
    · have : (fun x => ∫ t, ‖F (x, t)‖) = fun x => Real.exp (-s.re * x) * ∫ u, ‖h u‖ := by
        funext x
        simp_rw [hFeq, norm_mul, Complex.norm_exp]
        rw [integral_const_mul, integral_sub_right_eq_self (fun u => ‖h u‖) x]
        congr 2; simp
      rw [this]
      exact hU.mul_const _
  have hinner : ∀ t : ℝ, ∫ x, F (x, t) ∂U =
      Complex.exp (-s * (t : ℂ)) * ((∫ x, cdfOf ν (t - x) ∂U : ℝ) : ℂ) := by
    intro t
    simp only [hF]
    rw [integral_const_mul]; congr 1; exact integral_ofReal
  constructor
  · have := hFint.integral_prod_right
    simp_rw [hinner] at this
    exact this
  · unfold twoSidedLaplace
    simp_rw [← hinner]
    have := integral_integral_swap (f := fun x t => F (x, t)) hFint
    rw [← this]
    have h2 : ∀ x : ℝ, ∫ t, F (x, t) = Complex.exp (-(s * (x : ℂ))) * ∫ t, h t := by
      intro x
      simp_rw [hFeq]
      rw [integral_const_mul, integral_sub_right_eq_self h x, neg_mul]
    simp_rw [h2]
    unfold QueueingFundamentals.MG1.lst
    rw [integral_mul_const, mul_comm]

theorem wiener_hopf_core (A B ν : Measure ℝ) (hA : IsLifetimeLaw A) (hB : IsLifetimeLaw B)
    (hν : IsStationaryDelay A B ν) :
    (∀ t : ℝ, negPart (diffLaw A B) (cdfOf ν) t + cdfOf ν t =
        ∫ x in Set.Iic t, cdfOf ν (t - x) ∂(diffLaw A B)) ∧
    ∀ s : ℂ, 0 < s.re → Integrable (fun x : ℝ => Real.exp (s.re * x)) A →
      QueueingFundamentals.MG1.lst (diffLaw A B) s = QueueingFundamentals.MG1.lst A (-s) * QueueingFundamentals.MG1.lst B s ∧
      twoSidedLaplace (negPart (diffLaw A B) (cdfOf ν)) s + twoSidedLaplace (cdfOf ν) s =
        twoSidedLaplace (cdfOf ν) s * (QueueingFundamentals.MG1.lst A (-s) * QueueingFundamentals.MG1.lst B s) ∧
      (QueueingFundamentals.MG1.lst A (-s) * QueueingFundamentals.MG1.lst B s ≠ 1 →
        twoSidedLaplace (cdfOf ν) s =
          twoSidedLaplace (negPart (diffLaw A B) (cdfOf ν)) s / (QueueingFundamentals.MG1.lst A (-s) * QueueingFundamentals.MG1.lst B s - 1)) := by
  obtain ⟨hAp, hA0⟩ := hA
  obtain ⟨hBp, hB0⟩ := hB
  obtain ⟨hνp, hst⟩ := hν
  have := hAp; have := hBp; have := hνp
  haveI : IsProbabilityMeasure (diffLaw A B) := qf_diffLaw_prob A B
  have hneg := qf_stat_neg hst
  refine ⟨fun t => qf_part1 hst t, ?_⟩
  intro s hs hAint
  have hlst := qf_lst_diff A B s
  have hUint := qf_expU_int A B hB0 s.re hs hAint
  obtain ⟨hGint, hGlap⟩ := qf_lap_conv (diffLaw A B) ν hneg s hs hUint
  have hWint := qf_lap_int ν hneg s hs
  have hpt : ∀ t : ℝ, Complex.exp (-s * (t : ℂ)) * (negPart (diffLaw A B) (cdfOf ν) t : ℂ) =
      Complex.exp (-s * (t : ℂ)) * ((∫ x, cdfOf ν (t - x) ∂(diffLaw A B) : ℝ) : ℂ) -
      Complex.exp (-s * (t : ℂ)) * (cdfOf ν t : ℂ) := by
    intro t
    have := qf_part1 hst t
    rw [qf_full_eq_Iic ν _ hneg t] at this
    rw [← this]; push_cast; ring
  have hsum : twoSidedLaplace (negPart (diffLaw A B) (cdfOf ν)) s + twoSidedLaplace (cdfOf ν) s =
      twoSidedLaplace (cdfOf ν) s * (QueueingFundamentals.MG1.lst A (-s) * QueueingFundamentals.MG1.lst B s) := by
    rw [← hlst, ← hGlap]
    unfold twoSidedLaplace
    simp_rw [hpt]
    rw [integral_sub hGint hWint]
    ring
  refine ⟨hlst, hsum, fun hne => ?_⟩
  have hne' : QueueingFundamentals.MG1.lst A (-s) * QueueingFundamentals.MG1.lst B s - 1 ≠ 0 :=
    sub_ne_zero.mpr hne
  rw [eq_div_iff hne']
  linear_combination -hsum

end QueueingFundamentals.GG1

open QueueingFundamentals.GG1
open MeasureTheory

theorem solution (A B ν : Measure ℝ) (hA : IsLifetimeLaw A) (hB : IsLifetimeLaw B)
    (hν : IsStationaryDelay A B ν) :
    (∀ t : ℝ, negPart (diffLaw A B) (cdfOf ν) t + cdfOf ν t =
        ∫ x in Set.Iic t, cdfOf ν (t - x) ∂(diffLaw A B)) ∧
    ∀ s : ℂ, 0 < s.re → Integrable (fun x : ℝ => Real.exp (s.re * x)) A →
      QueueingFundamentals.MG1.lst (diffLaw A B) s = QueueingFundamentals.MG1.lst A (-s) * QueueingFundamentals.MG1.lst B s ∧
      twoSidedLaplace (negPart (diffLaw A B) (cdfOf ν)) s + twoSidedLaplace (cdfOf ν) s =
        twoSidedLaplace (cdfOf ν) s * (QueueingFundamentals.MG1.lst A (-s) * QueueingFundamentals.MG1.lst B s) ∧
      (QueueingFundamentals.MG1.lst A (-s) * QueueingFundamentals.MG1.lst B s ≠ 1 →
        twoSidedLaplace (cdfOf ν) s =
          twoSidedLaplace (negPart (diffLaw A B) (cdfOf ν)) s / (QueueingFundamentals.MG1.lst A (-s) * QueueingFundamentals.MG1.lst B s - 1)) := by
  exact wiener_hopf_core A B ν hA hB hν

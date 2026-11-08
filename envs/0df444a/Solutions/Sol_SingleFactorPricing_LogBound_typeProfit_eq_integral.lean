-- Prove2me | solution 1 for SingleFactorPricing.LogBound.typeProfit_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T03:31:02.616599+00:00
-- url     : https://prove2.me/submissions/f70bb886-b5c5-4c33-9079-5c9727c620af

import Mathlib
import Definitions.Def_SingleFactorPricing_LogBound_typeProfit
import Definitions.Def_SingleFactorPricing_LogBound_typeFilteredDemand

open MeasureTheory

open SingleFactorPricing.LogBound in
theorem solution {N T : Type*} [Fintype N] (d : T → (N → ℝ) → N → ℝ) (f : N → ℝ)
    (pbar : T → N → ℝ) (t : T) (hf : ∀ i, 0 < f i) (hp : ∀ i, 0 < pbar t i) :
    IntegrableOn (typeFilteredDemand d f pbar t) (Set.Ioi 0) ∧
      typeProfit d t (pbar t) = ∫ q in Set.Ioi (0 : ℝ), typeFilteredDemand d f pbar t q := by
  have hb : ∀ i, Set.Iic (pbar t i / f i) ∩ Set.Ioi 0 = Set.Ioc 0 (pbar t i / f i) := by
    intro i; ext q; simp [and_comm]
  have hg : ∀ i, (fun q => f i * d t (pbar t) i * filterIndicator f pbar t i q) =
      (Set.Iic (pbar t i / f i)).indicator (fun _ => f i * d t (pbar t) i) := by
    intro i; funext q
    unfold filterIndicator
    by_cases h : q ≤ pbar t i / f i
    · rw [if_pos h, Set.indicator_of_mem (show q ∈ Set.Iic (pbar t i / f i) from h), mul_one]
    · rw [if_neg h, Set.indicator_of_notMem (show q ∉ Set.Iic (pbar t i / f i) from h), mul_zero]
  have hint : ∀ i, Integrable (fun q => f i * d t (pbar t) i * filterIndicator f pbar t i q)
      (volume.restrict (Set.Ioi 0)) := by
    intro i
    rw [hg i]
    apply (integrable_indicator_iff measurableSet_Iic).mpr
    refine integrableOn_const ?_
    rw [Measure.restrict_apply measurableSet_Iic, hb i, Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hfun : typeFilteredDemand d f pbar t =
      fun q => ∑ i, f i * d t (pbar t) i * filterIndicator f pbar t i q := rfl
  constructor
  · rw [hfun]
    show Integrable _ (volume.restrict _)
    exact integrable_finsetSum _ (fun i _ => hint i)
  · rw [hfun, integral_finsetSum _ (fun i _ => hint i)]
    unfold typeProfit
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hg i, integral_indicator_const _ measurableSet_Iic, measureReal_restrict_apply measurableSet_Iic,
      hb i, Real.volume_real_Ioc_of_le (div_pos (hp i) (hf i)).le, smul_eq_mul, sub_zero]
    have := (hf i).ne'
    first | (field_simp; ring) | field_simp

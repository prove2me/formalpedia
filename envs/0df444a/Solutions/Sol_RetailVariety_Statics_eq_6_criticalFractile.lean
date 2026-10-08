-- Prove2me | solution 1 for RetailVariety.Statics.eq_6_criticalFractile
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:22:54.166593+00:00
-- url     : https://prove2.me/submissions/9de5fe5e-0182-4c0d-8087-0dea7af28c59

import Mathlib
import Definitions.Def_RetailVariety_Statics_Model

open Filter Topology MeasureTheory ProbabilityTheory Set RetailVariety.Statics

namespace Round35

lemma normal_strict : StrictMono (cdf (gaussianReal 0 1)) := by
  intro a b hab
  have hn : gaussianReal 0 1 (Ioc a b) ≠ 0 := by
    intro hz
    have hv := gaussianReal_absolutelyContinuous' (0:ℝ) (show (1:NNReal) ≠ 0 by norm_num) hz
    have hv' : b ≤ a := by simpa [Real.volume_Ioc] using hv
    exact (not_le.mpr hab) hv'
  have he := (cdf (gaussianReal 0 1)).measure_Ioc a b
  rw [measure_cdf] at he
  have hp : 0 < ENNReal.ofReal (cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a) := by
    rw [← he]; exact pos_iff_ne_zero.mpr hn
  exact sub_pos.mp (ENNReal.ofReal_pos.mp hp)

lemma normal_cont : Continuous (cdf (gaussianReal 0 1)) := by
  letI := nullSingletonClass_gaussianReal (μ := (0:ℝ)) (show (1:NNReal) ≠ 0 by norm_num)
  apply continuous_iff_continuousAt.mpr
  intro a
  have he := (cdf (gaussianReal 0 1)).measure_singleton a
  rw [measure_cdf, measure_singleton] at he
  have hl : Function.leftLim (cdf (gaussianReal 0 1)) a = cdf (gaussianReal 0 1) a := by
    have hh := ENNReal.ofReal_eq_zero.mp he.symm
    have hle := (monotone_cdf (gaussianReal 0 1)).leftLim_le (x := a) le_rfl
    linarith
  apply (monotone_cdf (gaussianReal 0 1)).continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [hl, (cdf (gaussianReal 0 1)).rightLim_eq]

end Round35

theorem solution (p c : ℝ) (hc : 0 < c) (hcp : c < p) :
    stdNormalCdf (criticalFractile p c) = 1 - c / p ∧
      ∀ x : ℝ, stdNormalCdf x = 1 - c / p → x = criticalFractile p c := by
  have hp : 0 < p := lt_trans hc hcp
  have hr0 : 0 < 1-c/p := by have := (div_lt_one hp).mpr hcp; linarith
  have hr1 : 1-c/p < 1 := by have := div_pos hc hp; linarith
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot (gaussianReal 0 1)).eventually
    (eventually_lt_nhds hr0)).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop (gaussianReal 0 1)).eventually
    (eventually_gt_nhds hr1)).exists
  obtain ⟨z, hz⟩ := intermediate_value_univ a b Round35.normal_cont ⟨ha.le, hb.le⟩
  have hset : {x : ℝ | 1-c/p ≤ cdf (gaussianReal 0 1) x} = Ici z := by
    ext x
    simp only [mem_setOf_eq, mem_Ici]
    rw [← hz]
    exact Round35.normal_strict.le_iff_le
  have heq : criticalFractile p c = z := by
    change sInf {x : ℝ | 1-c/p ≤ cdf (gaussianReal 0 1) x} = z
    rw [hset, csInf_Ici]
  refine ⟨by simpa [heq, stdNormalCdf] using hz, ?_⟩
  intro x hx
  rw [heq]
  exact Round35.normal_strict.injective (by simpa [stdNormalCdf, hz] using hx)

#print axioms solution

-- Prove2me | solution 1 for SepMeasures.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:02:55.695799+00:00
-- url     : https://prove2.me/submissions/f0a2630d-ddf2-41ea-80de-1489440d2b92

import Mathlib
import Definitions.Def_SepMeasures_Hyp

open MeasureTheory SepMeasures

namespace Aux24

lemma measurableSet_hyp_pos {d : ℕ} (K : Hyp d) : MeasurableSet K.pos :=
  isOpen_lt continuous_const (continuous_const.inner continuous_id) |>.measurableSet

lemma measurableSet_hyp_neg {d : ℕ} (K : Hyp d) : MeasurableSet K.neg :=
  isOpen_lt (continuous_const.inner continuous_id) continuous_const |>.measurableSet

lemma measurable_sign {d : ℕ} (K : Hyp d) : Measurable K.sign := by
  unfold Hyp.sign
  exact Measurable.ite (measurableSet_hyp_pos K) measurable_const
    (Measurable.ite (measurableSet_hyp_neg K) measurable_const measurable_const)

lemma measurableSet_sep {d : ℕ} (K : Hyp d) : MeasurableSet (SepMeasures.Sep K) :=
  ((measurableSet_hyp_pos K).prod (measurableSet_hyp_neg K)).union
    ((measurableSet_hyp_neg K).prod (measurableSet_hyp_pos K))

lemma integrable_sign {d : ℕ} (μ : Measure (E d)) [IsFiniteMeasure μ] (K : Hyp d) :
    Integrable K.sign μ := by
  refine Integrable.of_bound (measurable_sign K).aestronglyMeasurable 1 (ae_of_all μ fun x => ?_)
  unfold Hyp.sign
  split_ifs <;> norm_num

lemma prod_ae_not_mem_set {d : ℕ} {μ ν : Measure (E d)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {S T : Set (E d)} (hS : μ S = 0) (hT : ν T = 0) :
    ∀ᵐ p ∂(μ.prod ν), p.1 ∉ S ∧ p.2 ∉ T := by
  have h1 : (μ.prod ν) (S ×ˢ Set.univ) = 0 := by
    rw [Measure.prod_prod, hS, zero_mul]
  have h2 : (μ.prod ν) (Set.univ ×ˢ T) = 0 := by
    rw [Measure.prod_prod, hT, mul_zero]
  have hunion : (μ.prod ν) ((S ×ˢ Set.univ) ∪ (Set.univ ×ˢ T)) = 0 :=
    measure_union_null h1 h2
  rw [ae_iff]
  refine measure_mono_null (fun p hp => ?_) hunion
  simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, and_true, true_and]
  by_contra h
  push Not at h
  exact hp h

end Aux24

theorem solution (d : ℕ) (hd : 1 ≤ d) (μ ν : Measure (E d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : Hyp d) (hμ : μ K.set = 0) (hν : ν K.set = 0) :
    (μ.prod ν).real (Sep K) = (1 - (∫ x, K.sign x ∂μ) * (∫ y, K.sign y ∂ν)) / 2 := by
  have _ := hd
  rw [← integral_indicator_one (Aux24.measurableSet_sep K)]
  have hae : (SepMeasures.Sep K).indicator (1 : E d × E d → ℝ) =ᵐ[μ.prod ν]
      fun p => (1 - K.sign p.1 * K.sign p.2) / 2 := by
    filter_upwards [Aux24.prod_ae_not_mem_set hμ hν] with ⟨x, y⟩ ⟨hx, hy⟩
    have hxc : inner ℝ K.u x ≠ K.c := hx
    have hyc : inner ℝ K.u y ≠ K.c := hy
    unfold SepMeasures.Sep Hyp.pos Hyp.neg Hyp.sign
    rcases lt_or_gt_of_ne hxc with hxl | hxg <;> rcases lt_or_gt_of_ne hyc with hyl | hyg
    · simp [Set.indicator_apply, hxl, hyl, not_lt.mpr hxl.le, not_lt.mpr hyl.le]
    · simp [Set.indicator_apply, hxl, hyg, not_lt.mpr hxl.le, not_lt.mpr hyg.le]
    · simp [Set.indicator_apply, hxg, hyl, not_lt.mpr hxg.le, not_lt.mpr hyl.le]
    · simp [Set.indicator_apply, hxg, hyg, not_lt.mpr hxg.le, not_lt.mpr hyg.le]
  rw [integral_congr_ae hae]
  have hint1 : Integrable (fun _ : E d × E d => (1 : ℝ)) (μ.prod ν) := integrable_const 1
  have hint2 : Integrable (fun p : E d × E d => K.sign p.1 * K.sign p.2) (μ.prod ν) :=
    (Aux24.integrable_sign μ K).mul_prod (Aux24.integrable_sign ν K)
  rw [integral_div, integral_sub hint1 hint2, integral_const, probReal_univ, one_smul,
    integral_prod_mul]

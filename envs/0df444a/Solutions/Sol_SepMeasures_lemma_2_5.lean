-- Prove2me | solution 1 for SepMeasures.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:12:56.514949+00:00
-- url     : https://prove2.me/submissions/57fbb02c-f4f9-42cb-82f1-922a445f399a

import Mathlib
import Definitions.Def_SepMeasures_Hyp

open MeasureTheory SepMeasures

namespace Aux25

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

lemma integrable_sign_mul {d : ℕ} (μ : Measure (E d)) [IsFiniteMeasure μ] (K K' : Hyp d) :
    Integrable (fun x => K.sign x * K'.sign x) μ := by
  refine Integrable.of_bound
    ((measurable_sign K).mul (measurable_sign K')).aestronglyMeasurable 1 (ae_of_all μ fun x => ?_)
  have h1 : |K.sign x| ≤ 1 := by unfold Hyp.sign; split_ifs <;> norm_num
  have h2 : |K'.sign x| ≤ 1 := by unfold Hyp.sign; split_ifs <;> norm_num
  simpa [abs_mul] using mul_le_one₀ h1 (abs_nonneg _) h2

lemma sep_indicator_eq {d : ℕ} (K : Hyp d) {x y : E d}
    (hx : x ∉ K.set) (hy : y ∉ K.set) :
    (SepMeasures.Sep K).indicator (1 : E d × E d → ℝ) (x, y) = (1 - K.sign x * K.sign y) / 2 := by
  have hxc : inner ℝ K.u x ≠ K.c := hx
  have hyc : inner ℝ K.u y ≠ K.c := hy
  unfold SepMeasures.Sep Hyp.pos Hyp.neg Hyp.sign
  rcases lt_or_gt_of_ne hxc with hxl | hxg <;> rcases lt_or_gt_of_ne hyc with hyl | hyg
  · simp [Set.indicator_apply, hxl, hyl, not_lt.mpr hxl.le, not_lt.mpr hyl.le]
  · simp [Set.indicator_apply, hxl, hyg, not_lt.mpr hxl.le, not_lt.mpr hyg.le]
  · simp [Set.indicator_apply, hxg, hyl, not_lt.mpr hxg.le, not_lt.mpr hyl.le]
  · simp [Set.indicator_apply, hxg, hyg, not_lt.mpr hxg.le, not_lt.mpr hyg.le]

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

end Aux25

theorem solution (d : ℕ) (hd : 1 ≤ d) (μ ν : Measure (E d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K K' : Hyp d) (hμ : μ (K.set ∪ K'.set) = 0) (hν : ν (K.set ∪ K'.set) = 0) :
    (μ.prod ν).real (Sep K ∩ Sep K') =
      (1 - (∫ x, K.sign x ∂μ) * (∫ y, K.sign y ∂ν)
          - (∫ x, K'.sign x ∂μ) * (∫ y, K'.sign y ∂ν)
          + (∫ x, K.sign x * K'.sign x ∂μ) * (∫ y, K.sign y * K'.sign y ∂ν)) / 4 := by
  have _ := hd
  rw [← integral_indicator_one ((Aux25.measurableSet_sep K).inter (Aux25.measurableSet_sep K'))]
  have hae : (SepMeasures.Sep K ∩ SepMeasures.Sep K').indicator (1 : E d × E d → ℝ) =ᵐ[μ.prod ν]
      fun p => (1 - K.sign p.1 * K.sign p.2 - K'.sign p.1 * K'.sign p.2 +
        (K.sign p.1 * K'.sign p.1) * (K.sign p.2 * K'.sign p.2)) / 4 := by
    filter_upwards [Aux25.prod_ae_not_mem_set hμ hν] with ⟨x, y⟩ ⟨hx, hy⟩
    simp only [Set.mem_union, not_or] at hx hy
    have h1 := Aux25.sep_indicator_eq K hx.1 hy.1
    have h2 := Aux25.sep_indicator_eq K' hx.2 hy.2
    have hind : (SepMeasures.Sep K ∩ SepMeasures.Sep K').indicator (1 : E d × E d → ℝ) (x, y) =
        (SepMeasures.Sep K).indicator (1 : E d × E d → ℝ) (x, y) *
          (SepMeasures.Sep K').indicator (1 : E d × E d → ℝ) (x, y) := by
      by_cases hk : (x, y) ∈ SepMeasures.Sep K <;> by_cases hk' : (x, y) ∈ SepMeasures.Sep K' <;>
        simp [hk, hk']
    rw [hind, h1, h2]
    ring
  rw [integral_congr_ae hae, integral_div]
  have i1 : Integrable (fun _ : E d × E d => (1 : ℝ)) (μ.prod ν) := integrable_const 1
  have iK : Integrable (fun p : E d × E d => K.sign p.1 * K.sign p.2) (μ.prod ν) :=
    (Aux25.integrable_sign μ K).mul_prod (Aux25.integrable_sign ν K)
  have iK' : Integrable (fun p : E d × E d => K'.sign p.1 * K'.sign p.2) (μ.prod ν) :=
    (Aux25.integrable_sign μ K').mul_prod (Aux25.integrable_sign ν K')
  have iKK' : Integrable (fun p : E d × E d =>
      (K.sign p.1 * K'.sign p.1) * (K.sign p.2 * K'.sign p.2)) (μ.prod ν) :=
    (Aux25.integrable_sign_mul μ K K').mul_prod (Aux25.integrable_sign_mul ν K K')
  have i1K : Integrable (fun p : E d × E d => 1 - K.sign p.1 * K.sign p.2) (μ.prod ν) :=
    i1.sub iK
  have i1KK' : Integrable (fun p : E d × E d =>
      1 - K.sign p.1 * K.sign p.2 - K'.sign p.1 * K'.sign p.2) (μ.prod ν) :=
    i1K.sub iK'
  rw [integral_add i1KK' iKK', integral_sub i1K iK', integral_sub i1 iK,
    integral_const, probReal_univ, one_smul,
    integral_prod_mul K.sign K.sign,
    integral_prod_mul K'.sign K'.sign,
    integral_prod_mul (fun x => K.sign x * K'.sign x) (fun y => K.sign y * K'.sign y)]

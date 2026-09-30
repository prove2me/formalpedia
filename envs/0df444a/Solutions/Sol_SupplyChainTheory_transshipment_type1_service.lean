-- Prove2me | solution 1 for SupplyChainTheory.transshipment_type1_service
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T04:40:11.594175+00:00
-- url     : https://prove2.me/submissions/52f72247-7160-4dd7-93ba-19a4f43c16e3

import Mathlib
import Definitions.Def_SupplyChainTheory_flexibility

open MeasureTheory ProbabilityTheory

namespace SupplyChainTheory

section Type1

lemma ts_meas (Sj Si : ℝ) : Measurable (fun q : ℝ × ℝ => transship Sj Si q.1 q.2) := by
  unfold transship
  apply Measurable.ite
  · exact (measurableSet_lt measurable_fst measurable_const).inter
      (measurableSet_lt measurable_const measurable_snd)
  · exact (measurable_const.sub measurable_fst).min (measurable_snd.sub measurable_const)
  · exact measurable_const

lemma ts_nonneg (Sj Si dj di : ℝ) : 0 ≤ transship Sj Si dj di := by
  unfold transship
  split_ifs with h
  · exact le_min (by linarith [h.1]) (by linarith [h.2])
  · exact le_rfl

lemma ts_le (Sj Si dj di : ℝ) : transship Sj Si dj di ≤ max (di - Si) 0 := by
  unfold transship
  split_ifs with h
  · exact (min_le_right _ _).trans (le_max_left _ _)
  · exact le_max_right _ _

/-- Lipschitz form of the transshipment in the receiving level. -/
lemma ts_lip_form (Sj s dj di : ℝ) :
    transship Sj s dj di = if dj < Sj then max (min (Sj - dj) (di - s)) 0 else 0 := by
  unfold transship
  by_cases h1 : dj < Sj
  · rw [if_pos h1]
    by_cases h2 : s < di
    · rw [if_pos ⟨h1, h2⟩, max_eq_left (le_min (by linarith) (by linarith))]
    · rw [if_neg (fun h => h2 h.2), max_eq_right ((min_le_right _ _).trans (by linarith))]
  · rw [if_neg (fun h => h1 h.1), if_neg h1]

lemma ts_lip (Sj dj di : ℝ) :
    LipschitzWith 1 (fun s => transship Sj s dj di) := by
  have e : (fun s => transship Sj s dj di) =
      fun s => if dj < Sj then max (min (Sj - dj) (di - s)) 0 else 0 := funext fun s =>
    ts_lip_form Sj s dj di
  rw [e]
  by_cases h1 : dj < Sj
  · simp only [if_pos h1]
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    calc |max (min (Sj - dj) (di - x)) 0 - max (min (Sj - dj) (di - y)) 0|
        ≤ |min (Sj - dj) (di - x) - min (Sj - dj) (di - y)| := abs_max_sub_max_le_abs _ _ _
      _ ≤ max |(Sj - dj) - (Sj - dj)| |(di - x) - (di - y)| := abs_min_sub_min_le_max _ _ _ _
      _ = |x - y| := by
          rw [sub_self, abs_zero, show di - x - (di - y) = -(x - y) by ring, abs_neg]
          exact max_eq_right (abs_nonneg _)
  · simp only [if_neg h1]
    exact (LipschitzWith.const (0:ℝ)).weaken zero_le

lemma ts_deriv (Sj Si dj di : ℝ) (h1 : di ≠ Si) (h2 : di - Si ≠ Sj - dj) :
    HasDerivAt (fun s => transship Sj s dj di)
      (if dj < Sj ∧ Si < di ∧ di - Si < Sj - dj then (-1:ℝ) else 0) Si := by
  by_cases hj : dj < Sj
  · rcases lt_or_gt_of_ne h1 with hlt | hgt
    · rw [if_neg (fun h => by linarith [h.2.1])]
      apply (hasDerivAt_const Si (0:ℝ)).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hlt] with s hs
      unfold transship
      rw [if_neg (fun h => by linarith [h.2, show di < s from hs])]
    · rcases lt_or_gt_of_ne h2 with h3 | h3
      · rw [if_pos ⟨hj, hgt, h3⟩]
        have hd : HasDerivAt (fun s => di - s) (-1) Si := by
          simpa using (hasDerivAt_id Si).const_sub di
        apply hd.congr_of_eventuallyEq
        have e1 : ∀ᶠ s in nhds Si, s < di := Iio_mem_nhds hgt
        have e2 : ∀ᶠ s in nhds Si, di - (Sj - dj) < s := Ioi_mem_nhds (by linarith)
        filter_upwards [e1, e2] with s hs1 hs2
        unfold transship
        rw [if_pos ⟨hj, hs1⟩, min_eq_right (by linarith)]
      · rw [if_neg (fun h => by linarith [h.2.2])]
        apply (hasDerivAt_const Si (Sj - dj)).congr_of_eventuallyEq
        have e1 : ∀ᶠ s in nhds Si, s < di := Iio_mem_nhds hgt
        have e2 : ∀ᶠ s in nhds Si, s < di - (Sj - dj) := Iio_mem_nhds (by linarith)
        filter_upwards [e1, e2] with s hs1 hs2
        unfold transship
        rw [if_pos ⟨hj, hs1⟩, min_eq_left (by linarith)]
  · rw [if_neg (fun h => hj h.1)]
    apply (hasDerivAt_const Si (0:ℝ)).congr_of_eventuallyEq
    filter_upwards with s
    unfold transship
    rw [if_neg (fun h => hj h.1)]

lemma null_bdry (Dj Di : Measure ℝ) [IsProbabilityMeasure Dj] [IsProbabilityMeasure Di]
    [NullSingletonClass Di] (Sj Si : ℝ) :
    ∀ᵐ q ∂(Dj.prod Di), q.2 ≠ Si ∧ q.2 - Si ≠ Sj - q.1 := by
  have hA : (Dj.prod Di) {q : ℝ × ℝ | q.2 = Si} = 0 := by
    have e : {q : ℝ × ℝ | q.2 = Si} = Set.univ ×ˢ {Si} := by ext q; simp
    rw [e, Measure.prod_prod, measure_singleton, mul_zero]
  have hB : (Dj.prod Di) {q : ℝ × ℝ | q.2 - Si = Sj - q.1} = 0 := by
    have hm : MeasurableSet {q : ℝ × ℝ | q.2 - Si = Sj - q.1} :=
      measurableSet_eq_fun (measurable_snd.sub measurable_const) (measurable_const.sub measurable_fst)
    rw [Measure.prod_apply hm]
    have hz : ∀ x : ℝ, Di (Prod.mk x ⁻¹' {q : ℝ × ℝ | q.2 - Si = Sj - q.1}) = 0 := by
      intro x
      have e : Prod.mk x ⁻¹' {q : ℝ × ℝ | q.2 - Si = Sj - q.1} = {Si + Sj - x} := by
        ext y
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor <;> intro h <;> linarith
      rw [e, measure_singleton]
    exact (lintegral_congr hz).trans lintegral_zero
  have hU := measure_union_null hA hB
  rw [ae_iff]
  apply measure_mono_null _ hU
  intro q hq
  simp only [Set.mem_setOf_eq, not_and_or, not_not] at hq
  rcases hq with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem type1_main (Sj Si : ℝ) (Dj Di : Measure ℝ)
    [IsProbabilityMeasure Dj] [IsProbabilityMeasure Di]
    [NullSingletonClass Dj] [NullSingletonClass Di]
    (hj : Integrable (fun x => x) Dj) (hi : Integrable (fun x => x) Di) :
    ∃ dY : ℝ, HasDerivAt (fun s => expTransship Sj s Dj Di) dY Si ∧ dY ≤ 0
      ∧ type1Trans Sj Si Dj Di = type1NoTrans Si Di + |dY| := by
  set μ := Dj.prod Di with hμ
  set E : Set (ℝ × ℝ) := {q | q.1 < Sj ∧ Si < q.2 ∧ q.2 - Si < Sj - q.1} with hE
  have hEm : MeasurableSet E :=
    (measurableSet_lt measurable_fst measurable_const).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt (measurable_snd.sub measurable_const) (measurable_const.sub measurable_fst)))
  set F' : ℝ × ℝ → ℝ := fun q => if q.1 < Sj ∧ Si < q.2 ∧ q.2 - Si < Sj - q.1 then -1 else 0
    with hF'
  have hF'm : Measurable F' := Measurable.ite hEm measurable_const measurable_const
  have hplus : Integrable (fun d : ℝ => max (d - Si) 0) Di := by
    refine Integrable.mono' (hi.abs.add (integrable_const |Si|))
      ((measurable_id.sub measurable_const).max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun d => ?_)
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · linarith [le_abs_self d, neg_abs_le Si]
    · positivity
  have hint : Integrable (fun q : ℝ × ℝ => transship Sj Si q.1 q.2) μ := by
    refine Integrable.mono' (hplus.comp_snd Dj) (ts_meas Sj Si).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (ts_nonneg _ _ _ _)]
    exact ts_le _ _ _ _
  have hlip : ∀ q : ℝ × ℝ, LipschitzOnWith (Real.nnabs 1)
      (fun s => transship Sj s q.1 q.2) Set.univ := by
    intro q
    have e : Real.nnabs 1 = 1 := by simp
    rw [e]
    exact (ts_lip Sj q.1 q.2).lipschitzOnWith
  have key := hasDerivAt_integral_of_dominated_loc_of_lip (μ := μ)
    (F := fun s q => transship Sj s q.1 q.2) (F' := F') (bound := fun _ => (1:ℝ))
    (s := Set.univ) (x₀ := Si) Filter.univ_mem
    (Filter.Eventually.of_forall fun s => (ts_meas Sj s).aestronglyMeasurable) hint
    hF'm.aestronglyMeasurable (Filter.Eventually.of_forall fun q => hlip q) (integrable_const 1)
    ((null_bdry Dj Di Sj Si).mono fun q hq => ts_deriv Sj Si q.1 q.2 hq.1 hq.2)
  have hF'int : ∫ q, F' q ∂μ = -μ.real E := by
    have e : F' = fun q => -(E.indicator 1 q) := by
      funext q
      simp only [hF', hE, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
      split_ifs <;> simp
    rw [e, integral_neg, integral_indicator_one hEm]
  refine ⟨-μ.real E, ?_, ?_, ?_⟩
  · rw [← hF'int]
    exact key.2
  · linarith [measureReal_nonneg (μ := μ) (s := E)]
  · rw [abs_neg, abs_of_nonneg measureReal_nonneg]
    have hL : MeasurableSet {q : ℝ × ℝ | q.2 ≤ Si} := measurableSet_le measurable_snd measurable_const
    have hdisj : Disjoint {q : ℝ × ℝ | q.2 ≤ Si} E := by
      rw [Set.disjoint_left]
      intro q hq hqE
      simp only [Set.mem_setOf_eq] at hq
      exact absurd hqE.2.1 (not_lt.mpr hq)
    have hae : ({q : ℝ × ℝ | q.2 - Si ≤ transship Sj Si q.1 q.2} : Set (ℝ × ℝ)) =ᵐ[μ]
        (({q : ℝ × ℝ | q.2 ≤ Si} ∪ E : Set (ℝ × ℝ))) := by
      filter_upwards [null_bdry Dj Di Sj Si] with q hq
      apply propext
      change q.2 - Si ≤ transship Sj Si q.1 q.2 ↔
        (q.2 ≤ Si ∨ (q.1 < Sj ∧ Si < q.2 ∧ q.2 - Si < Sj - q.1))
      constructor
      · intro h
        by_cases hq2 : q.2 ≤ Si
        · exact Or.inl hq2
        · push Not at hq2
          right
          unfold transship at h
          split_ifs at h with hc
          · refine ⟨hc.1, hq2, ?_⟩
            have h' : q.2 - Si ≤ Sj - q.1 := h.trans (min_le_left _ _)
            exact lt_of_le_of_ne h' hq.2
          · linarith
      · rintro (h | ⟨h1, h2, h3⟩)
        · linarith [ts_nonneg Sj Si q.1 q.2]
        · unfold transship
          rw [if_pos ⟨h1, h2⟩]
          exact le_min h3.le le_rfl
    have hNo : type1NoTrans Si Di = μ.real {q : ℝ × ℝ | q.2 ≤ Si} := by
      have e : {q : ℝ × ℝ | q.2 ≤ Si} = Set.univ ×ˢ Set.Iic Si := by ext q; simp
      unfold type1NoTrans
      rw [e, measureReal_prod_prod, probReal_univ, one_mul]
    unfold type1Trans
    rw [← hμ, measureReal_congr hae, measureReal_union hdisj hEm, hNo]

end Type1

end SupplyChainTheory

open SupplyChainTheory

theorem solution (Sj Si : ℝ) (Dj Di : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure Dj] [MeasureTheory.IsProbabilityMeasure Di]
    [MeasureTheory.NullSingletonClass Dj] [MeasureTheory.NullSingletonClass Di]
    (hj : MeasureTheory.Integrable (fun x => x) Dj)
    (hi : MeasureTheory.Integrable (fun x => x) Di) :
    ∃ dY : ℝ, HasDerivAt (fun s => expTransship Sj s Dj Di) dY Si ∧ dY ≤ 0
      ∧ type1Trans Sj Si Dj Di = type1NoTrans Si Di + |dY| := by
  exact type1_main Sj Si Dj Di hj hi

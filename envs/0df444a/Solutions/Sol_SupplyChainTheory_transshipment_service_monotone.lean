-- Prove2me | solution 1 for SupplyChainTheory.transshipment_service_monotone
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T04:33:18.819899+00:00
-- url     : https://prove2.me/submissions/aaa37a3c-0aaf-4907-806c-8516f58efd23

import Mathlib
import Definitions.Def_SupplyChainTheory_flexibility

open MeasureTheory ProbabilityTheory

namespace SupplyChainTheory

section Transship

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

lemma ts_pt (Sj Si dj di : ℝ) :
    max (di - Si - transship Sj Si dj di) 0 = max (di - Si) 0 - transship Sj Si dj di := by
  unfold transship
  split_ifs with h
  · have h1 : min (Sj - dj) (di - Si) ≤ di - Si := min_le_right _ _
    rw [max_eq_left (by linarith), max_eq_left (by linarith [h.2])]
  · simp

theorem type2_main (Sj Si : ℝ) (Dj Di : Measure ℝ)
    [IsProbabilityMeasure Dj] [IsProbabilityMeasure Di]
    (hj : Integrable (fun x => x) Dj) (hi : Integrable (fun x => x) Di) (hpos : 0 < ∫ d, d ∂Di) :
    type2Trans Sj Si Dj Di = type2NoTrans Si Di + expTransship Sj Si Dj Di / (∫ d, d ∂Di) := by
  have hplus : Integrable (fun d : ℝ => max (d - Si) 0) Di := by
    refine Integrable.mono' (hi.abs.add (integrable_const |Si|))
      ((measurable_id.sub measurable_const).max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun d => ?_)
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · linarith [le_abs_self d, neg_abs_le Si]
    · positivity
  have hplus2 : Integrable (fun q : ℝ × ℝ => max (q.2 - Si) 0) (Dj.prod Di) := hplus.comp_snd Dj
  have hY : Integrable (fun q : ℝ × ℝ => transship Sj Si q.1 q.2) (Dj.prod Di) := by
    refine Integrable.mono' hplus2 (ts_meas Sj Si).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (ts_nonneg _ _ _ _)]
    exact ts_le _ _ _ _
  have hint : ∫ q, max (q.2 - Si - transship Sj Si q.1 q.2) 0 ∂(Dj.prod Di) =
      (∫ d, max (d - Si) 0 ∂Di) - expTransship Sj Si Dj Di := by
    simp_rw [ts_pt]
    rw [integral_sub hplus2 hY, integral_fun_snd (fun d => max (d - Si) 0)]
    simp [expTransship]
  unfold type2Trans type2NoTrans
  rw [hint, sub_div]
  ring

lemma ts_closed (S1 S2 d1 d2 : ℝ) :
    max (d2 - S2 - transship S1 S2 d1 d2) 0 = max (d2 - S2 - max (S1 - d1) 0) 0 := by
  unfold transship
  split_ifs with h
  · rw [max_eq_left (by linarith [h.1] : (0:ℝ) ≤ S1 - d1)]
    rcases le_total (S1 - d1) (d2 - S2) with h' | h'
    · rw [min_eq_left h']
    · rw [min_eq_right h', sub_self, max_eq_right (by linarith : d2 - S2 - (S1 - d1) ≤ 0), max_self]
  · rw [sub_zero]
    by_cases hd1 : d1 < S1
    · have hd2 : d2 ≤ S2 := by
        by_contra hc; push Not at hc; exact h ⟨hd1, hc⟩
      rw [max_eq_right (by linarith : d2 - S2 ≤ 0), max_eq_left (by linarith : (0:ℝ) ≤ S1 - d1),
        max_eq_right (by linarith : d2 - S2 - (S1 - d1) ≤ 0)]
    · push Not at hd1
      rw [max_eq_right (by linarith : S1 - d1 ≤ 0), sub_zero]

lemma int_g (D1 D2 : Measure ℝ) [IsProbabilityMeasure D1] [IsProbabilityMeasure D2]
    (h2 : Integrable (fun x => x) D2) (S1 S2 : ℝ) :
    Integrable (fun q : ℝ × ℝ => max (q.2 - S2 - max (S1 - q.1) 0) 0) (D1.prod D2) := by
  have hplus : Integrable (fun d : ℝ => max (d - S2) 0) D2 := by
    refine Integrable.mono' (h2.abs.add (integrable_const |S2|))
      ((measurable_id.sub measurable_const).max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun d => ?_)
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · linarith [le_abs_self d, neg_abs_le S2]
    · positivity
  refine Integrable.mono' (hplus.comp_snd D1) ?_ (Filter.Eventually.of_forall fun q => ?_)
  · exact (((measurable_snd.sub measurable_const).sub
      ((measurable_const.sub measurable_fst).max measurable_const)).max
      measurable_const).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le_max (by linarith [le_max_right (S1 - q.1) 0]) le_rfl

theorem mono_main (Sj : ℝ) (Dj Di : Measure ℝ)
    [IsProbabilityMeasure Dj] [IsProbabilityMeasure Di]
    (hj : Integrable (fun x => x) Dj)
    (hi : Integrable (fun x => x) Di)
    (hposi : 0 < ∫ d, d ∂Di) (hposj : 0 < ∫ d, d ∂Dj) :
    Monotone (fun Si => type1Trans Sj Si Dj Di) ∧ Monotone (fun Si => type2Trans Sj Si Dj Di)
      ∧ Monotone (fun Si => type1Trans Si Sj Di Dj)
      ∧ Monotone (fun Si => type2Trans Si Sj Di Dj) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s s' hss
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro q hq
    simp only [Set.mem_setOf_eq] at hq ⊢
    by_cases hq2 : q.2 ≤ s'
    · linarith [ts_nonneg Sj s' q.1 q.2]
    · push Not at hq2
      unfold transship at hq ⊢
      split_ifs at hq with h
      · rw [if_pos ⟨h.1, hq2⟩]
        apply le_min _ le_rfl
        have := min_le_left (Sj - q.1) (q.2 - s)
        linarith
      · linarith
  · intro s s' hss
    simp only [type2Trans]
    simp_rw [ts_closed]
    have hI := integral_mono (int_g Dj Di hi Sj s') (int_g Dj Di hi Sj s)
      (fun q => max_le_max (by linarith) le_rfl)
    have := div_le_div_of_nonneg_right hI hposi.le
    linarith
  · intro s s' hss
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro q hq
    simp only [Set.mem_setOf_eq] at hq ⊢
    refine hq.trans ?_
    unfold transship
    split_ifs with h1 h2 h2
    · exact min_le_min (by linarith) le_rfl
    · exact absurd ⟨lt_of_lt_of_le h1.1 hss, h1.2⟩ h2
    · exact le_min (by linarith [h2.1]) (by linarith [h2.2])
    · exact le_rfl
  · intro s s' hss
    simp only [type2Trans]
    simp_rw [ts_closed]
    have hpt : ∀ q : ℝ × ℝ, max (q.2 - Sj - max (s' - q.1) 0) 0 ≤
        max (q.2 - Sj - max (s - q.1) 0) 0 := by
      intro q
      have hm : max (s - q.1) 0 ≤ max (s' - q.1) 0 := max_le_max (by linarith) le_rfl
      exact max_le_max (by linarith) le_rfl
    have hI := integral_mono (int_g Di Dj hj s' Sj) (int_g Di Dj hj s Sj) hpt
    have := div_le_div_of_nonneg_right hI hposj.le
    linarith

end Transship

end SupplyChainTheory

open SupplyChainTheory

theorem solution (Sj : ℝ) (Dj Di : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure Dj] [MeasureTheory.IsProbabilityMeasure Di]
    (hj : MeasureTheory.Integrable (fun x => x) Dj)
    (hi : MeasureTheory.Integrable (fun x => x) Di)
    (hposi : 0 < ∫ d, d ∂Di) (hposj : 0 < ∫ d, d ∂Dj) :
    Monotone (fun Si => type1Trans Sj Si Dj Di) ∧ Monotone (fun Si => type2Trans Sj Si Dj Di)
      ∧ Monotone (fun Si => type1Trans Si Sj Di Dj)
      ∧ Monotone (fun Si => type2Trans Si Sj Di Dj) := by
  exact mono_main Sj Dj Di hj hi hposi hposj

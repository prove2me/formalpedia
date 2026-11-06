-- Prove2me | solution 1 for WhittFLT.TimeReversal.theorem_8_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T04:52:59.966251+00:00
-- url     : https://prove2.me/submissions/08d66308-2b1c-428d-ad9b-b6be7ca4b83d

import Mathlib
import Definitions.Def_WhittFLT_TimeReversal_Reversal
import Theorems.Thm_WhittFLT_TimeReversal_revTime_mem
import Theorems.Thm_WhittFLT_TimeReversal_negRev_timeChange
import Theorems.Thm_WhittFLT_TimeReversal_supDist_revTime
import Theorems.Thm_WhittFLT_TimeReversal_revTime_comp_negRev

open Set Filter Topology
open scoped ENNReal

namespace Aux_WhittFLT_TimeReversal_theorem_8_1

open WhittFLT.TimeReversal WhittFLT.Composition

lemma tc_one (l : ℝ → ℝ) (hl : IsTimeChange 0 1 l) : l 1 = 1 := by
  obtain ⟨hmono, _, himg⟩ := hl
  have h0 : (1 : ℝ) ∈ l '' Icc 0 1 := by rw [himg]; exact ⟨zero_le_one, le_rfl⟩
  obtain ⟨s, hs, hs0⟩ := h0
  have hl0 : l 1 ∈ Icc (0 : ℝ) 1 := by rw [← himg]; exact mem_image_of_mem l ⟨zero_le_one, le_rfl⟩
  rcases eq_or_lt_of_le hs.2 with h | h
  · rw [h] at hs0; exact hs0
  · have := hmono hs ⟨zero_le_one, le_rfl⟩ h
    linarith [hl0.2]

lemma tc_maps (l : ℝ → ℝ) (hl : IsTimeChange 0 1 l) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    l t ∈ Icc (0 : ℝ) 1 := by
  rw [← hl.2.2]; exact mem_image_of_mem l ht

/-- `l` maps `Icc 0 1 ∩ T` filters at `t` into `Icc 0 1 ∩ T'` filters at `l t`. -/
lemma tc_tendsto_within (l : ℝ → ℝ) (hl : IsTimeChange 0 1 l) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (A B : Set ℝ) (hAB : ∀ s ∈ Icc (0 : ℝ) 1 ∩ A, l s ∈ B) :
    Tendsto l (𝓝[Icc 0 1 ∩ A] t) (𝓝[Icc 0 1 ∩ B] (l t)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨((hl.2.1 t ht).mono inter_subset_left).tendsto, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact ⟨tc_maps l hl hs.1, hAB s hs⟩

lemma leftLim_tendsto {S : Type*} [AddCommGroup S] [MetricSpace S] (x : ℝ → S) (hx : InD x)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    Tendsto x (𝓝[<] a) (𝓝 (Function.leftLim x a)) := by
  obtain ⟨l, hl⟩ := (hx.1 a ⟨ha0.le, ha1⟩).2
  have hmem : Icc (0 : ℝ) 1 ∈ 𝓝[<] a :=
    mem_of_superset (Ioo_mem_nhdsLT ha0) (fun u hu => ⟨hu.1.le, hu.2.le.trans ha1⟩)
  have heq : 𝓝[Icc (0 : ℝ) 1 ∩ Iio a] a = 𝓝[<] a := nhdsWithin_inter_of_mem hmem
  rw [heq] at hl
  rw [leftLim_eq_of_tendsto hl]
  exact hl

/-- Composition with a time change preserves `D`. -/
lemma comp_InD {S : Type*} [AddCommGroup S] [MetricSpace S] (x : ℝ → S) (hx : InD x)
    (l : ℝ → ℝ) (hl : IsTimeChange 0 1 l) : InD (x ∘ l) := by
  refine ⟨fun t ht => ⟨?_, ?_⟩, ?_⟩
  · have hxc := (hx.1 (l t) (tc_maps l hl ht)).1
    refine hxc.comp ((hl.2.1 t ht).mono inter_subset_left) ?_
    intro s hs
    refine ⟨tc_maps l hl hs.1, ?_⟩
    exact hl.1.monotoneOn ht hs.1 hs.2
  · obtain ⟨L, hL⟩ := (hx.1 (l t) (tc_maps l hl ht)).2
    refine ⟨L, hL.comp (tc_tendsto_within l hl t ht _ _ ?_)⟩
    intro s hs
    exact hl.1 hs.1 ht hs.2
  · have h1 : Icc (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) :=
      mem_of_superset (Ioo_mem_nhdsLT zero_lt_one) (fun u hu => ⟨hu.1.le, hu.2.le⟩)
    have hT := tc_tendsto_within l hl 1 ⟨zero_le_one, le_rfl⟩ (Iio 1) (Iio 1) (by
      intro s hs
      have := hl.1 hs.1 ⟨zero_le_one, le_rfl⟩ hs.2
      rw [tc_one l hl] at this; exact this)
    rw [nhdsWithin_inter_of_mem h1, tc_one l hl, nhdsWithin_inter_of_mem h1] at hT
    have h := (leftLim_tendsto x hx 1 zero_lt_one le_rfl).comp hT
    rw [leftLim_eq_of_tendsto h, hx.2, Function.comp_apply, tc_one l hl]

lemma supDist_congr_right {E : Type*} [PseudoEMetricSpace E] (x y y' : ℝ → E)
    (h : EqOn y y' (Icc 0 1)) : supDist 0 1 x y = supDist 0 1 x y' := by
  unfold supDist
  refine iSup_congr fun t => iSup_congr fun ht => ?_
  rw [h ht]

lemma supDist_negRev (l : ℝ → ℝ) : supDist 0 1 (negRev l) id = supDist 0 1 l id := by
  have key : ∀ t : ℝ, edist (negRev l t) (id t) = edist (l (1 - t)) (id (1 - t)) := by
    intro t
    simp only [negRev, id]
    rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq,
      show 1 - l (1 - t) - t = -(l (1 - t) - (1 - t)) by ring, abs_neg]
  unfold supDist
  apply le_antisymm
  · refine iSup₂_le fun t ht => ?_
    rw [key]
    exact le_iSup₂ (f := fun t (_ : t ∈ Icc (0 : ℝ) 1) => edist (l t) (id t)) (1 - t)
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · refine iSup₂_le fun t ht => ?_
    have := key (1 - t)
    rw [sub_sub_cancel] at this
    rw [← this]
    exact le_iSup₂ (f := fun t (_ : t ∈ Icc (0 : ℝ) 1) => edist (negRev l t) (id t)) (1 - t)
      ⟨by linarith [ht.2], by linarith [ht.1]⟩

lemma j1Dist_congr {S : Type*} [MetricSpace S] (x x' y y' : ℝ → S)
    (hx : EqOn x x' (Icc 0 1)) (hy : EqOn y y' (Icc 0 1)) :
    j1Dist 0 1 x y = j1Dist 0 1 x' y' := by
  unfold j1Dist
  refine iInf_congr fun l => iInf_congr fun hl => ?_
  congr 1
  unfold supDist
  refine iSup_congr fun t => iSup_congr fun ht => ?_
  simp only [Function.comp]
  rw [hx ht, hy (tc_maps l hl ht)]

lemma two_max_le (a b : ℝ≥0∞) : max a (2 * b) ≤ 2 * max a b := by
  apply max_le
  · calc a ≤ max a b := le_max_left _ _
      _ ≤ max a b + max a b := le_add_self
      _ = 2 * max a b := (two_mul _).symm
  · exact mul_le_mul_right (le_max_right _ _) 2

end Aux_WhittFLT_TimeReversal_theorem_8_1

open Aux_WhittFLT_TimeReversal_theorem_8_1 in
open WhittFLT.TimeReversal WhittFLT.Composition in
theorem solution {S : Type*} [AddCommGroup S] [MetricSpace S] [CompleteSpace S]
    [TopologicalSpace.SeparableSpace S] (hinv : ∀ a b c : S, dist (a + c) (b + c) = dist a b)
    (x y : ℝ → S) (hx : InD x) (hy : InD y) :
    WhittFLT.Composition.j1Dist 0 1 (revTime x) (revTime y) = WhittFLT.Composition.j1Dist 0 1 x y ∧
      WhittFLT.Composition.j1Dist 0 1 (revTime0 x) (revTime0 y) ≤ 2 * WhittFLT.Composition.j1Dist 0 1 x y := by
  -- the one-sided bound `d(Rx, Ry) ≤ d(x, y)` for all `x, y ∈ D`
  have hle : ∀ x y : ℝ → S, InD x → InD y → j1Dist 0 1 (revTime x) (revTime y) ≤ j1Dist 0 1 x y := by
    intro x y hx hy
    conv_rhs => unfold j1Dist
    refine le_iInf₂ fun l hl => ?_
    have hnl := (negRev_timeChange l hl).1
    have hyl := comp_InD y hy l hl
    calc j1Dist 0 1 (revTime x) (revTime y)
        ≤ max (supDist 0 1 (negRev l) id) (supDist 0 1 (revTime x) (revTime y ∘ negRev l)) :=
          iInf₂_le (f := fun l (_ : IsTimeChange 0 1 l) =>
            max (supDist 0 1 l id) (supDist 0 1 (revTime x) (revTime y ∘ l))) (negRev l) hnl
      _ = max (supDist 0 1 l id) (supDist 0 1 x (y ∘ l)) := by
          rw [supDist_negRev, supDist_congr_right _ _ _ (revTime_comp_negRev hinv y hy l hl).1,
            (supDist_revTime hinv x (y ∘ l) hx hyl).1]
  refine ⟨le_antisymm (hle x y hx hy) ?_, ?_⟩
  · have hRx := (revTime_mem hinv x hx)
    have hRy := (revTime_mem hinv y hy)
    have := hle (revTime x) (revTime y) hRx.1 hRy.1
    rwa [j1Dist_congr _ x _ y hRx.2.2.1 hRy.2.2.1] at this
  · have h2 : (2 : ℝ≥0∞) * j1Dist 0 1 x y = ⨅ (l : ℝ → ℝ) (_ : IsTimeChange 0 1 l),
        2 * max (supDist 0 1 l id) (supDist 0 1 x (y ∘ l)) := by
      unfold j1Dist
      rw [ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
      refine iInf_congr fun l => ?_
      rw [ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
    rw [h2]
    refine le_iInf₂ fun l hl => ?_
    have hnl := (negRev_timeChange l hl).1
    have hyl := comp_InD y hy l hl
    calc j1Dist 0 1 (revTime0 x) (revTime0 y)
        ≤ max (supDist 0 1 (negRev l) id) (supDist 0 1 (revTime0 x) (revTime0 y ∘ negRev l)) :=
          iInf₂_le (f := fun l (_ : IsTimeChange 0 1 l) =>
            max (supDist 0 1 l id) (supDist 0 1 (revTime0 x) (revTime0 y ∘ l))) (negRev l) hnl
      _ = max (supDist 0 1 l id) (supDist 0 1 (revTime0 x) (revTime0 (y ∘ l))) := by
          rw [supDist_negRev, supDist_congr_right _ _ _ (revTime_comp_negRev hinv y hy l hl).2]
      _ ≤ max (supDist 0 1 l id) (2 * supDist 0 1 x (y ∘ l)) :=
          max_le_max le_rfl (supDist_revTime hinv x (y ∘ l) hx hyl).2.2
      _ ≤ 2 * max (supDist 0 1 l id) (supDist 0 1 x (y ∘ l)) := two_max_le _ _

-- Prove2me | solution 1 for WhittFLT.TimeReversal.revTime_comp_negRev
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T04:49:52.663809+00:00
-- url     : https://prove2.me/submissions/4ff07d0f-bb26-4feb-ada7-c1be98af4028

import Mathlib
import Definitions.Def_WhittFLT_TimeReversal_Reversal

open Set Filter Topology

namespace Aux_WhittFLT_TimeReversal_revTime_comp_negRev

open WhittFLT.TimeReversal

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

lemma tc_zero (l : ℝ → ℝ) (hl : WhittFLT.Composition.IsTimeChange 0 1 l) : l 0 = 0 := by
  obtain ⟨hmono, _, himg⟩ := hl
  have h0 : (0 : ℝ) ∈ l '' Icc 0 1 := by rw [himg]; exact ⟨le_rfl, zero_le_one⟩
  obtain ⟨s, hs, hs0⟩ := h0
  have hl0 : l 0 ∈ Icc (0 : ℝ) 1 := by rw [← himg]; exact mem_image_of_mem l ⟨le_rfl, zero_le_one⟩
  rcases eq_or_lt_of_le hs.1 with h | h
  · rw [← h] at hs0; exact hs0
  · have := hmono ⟨le_rfl, zero_le_one⟩ hs h
    linarith [hl0.1]

lemma tc_one (l : ℝ → ℝ) (hl : WhittFLT.Composition.IsTimeChange 0 1 l) : l 1 = 1 := by
  obtain ⟨hmono, _, himg⟩ := hl
  have h0 : (1 : ℝ) ∈ l '' Icc 0 1 := by rw [himg]; exact ⟨zero_le_one, le_rfl⟩
  obtain ⟨s, hs, hs0⟩ := h0
  have hl0 : l 1 ∈ Icc (0 : ℝ) 1 := by rw [← himg]; exact mem_image_of_mem l ⟨zero_le_one, le_rfl⟩
  rcases eq_or_lt_of_le hs.2 with h | h
  · rw [h] at hs0; exact hs0
  · have := hmono hs ⟨zero_le_one, le_rfl⟩ h
    linarith [hl0.2]

lemma tc_tendsto_left (l : ℝ → ℝ) (hl : WhittFLT.Composition.IsTimeChange 0 1 l)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    Tendsto l (𝓝[<] a) (𝓝[<] (l a)) := by
  have hmem : Icc (0 : ℝ) 1 ∈ 𝓝[<] a :=
    mem_of_superset (Ioo_mem_nhdsLT ha0) (fun u hu => ⟨hu.1.le, hu.2.le.trans ha1⟩)
  have hc : ContinuousWithinAt l (Iio a) a :=
    (hl.2.1 a ⟨ha0.le, ha1⟩).mono_of_mem_nhdsWithin hmem
  rw [tendsto_nhdsWithin_iff]
  refine ⟨hc.tendsto, ?_⟩
  filter_upwards [Ioo_mem_nhdsLT ha0] with s hs
  exact hl.1 ⟨hs.1.le, hs.2.le.trans ha1⟩ ⟨ha0.le, ha1⟩ hs.2

lemma leftLim_comp {S : Type*} [AddCommGroup S] [MetricSpace S] (x : ℝ → S) (hx : InD x)
    (l : ℝ → ℝ) (hl : WhittFLT.Composition.IsTimeChange 0 1 l)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    Function.leftLim (x ∘ l) a = Function.leftLim x (l a) := by
  have hla0 : 0 < l a := by
    have := hl.1 ⟨le_rfl, zero_le_one⟩ ⟨ha0.le, ha1⟩ ha0
    rw [tc_zero l hl] at this; exact this
  have hla1 : l a ≤ 1 := by
    have : l a ∈ l '' Icc 0 1 := mem_image_of_mem l ⟨ha0.le, ha1⟩
    rw [hl.2.2] at this; exact this.2
  have h := (leftLim_tendsto x hx (l a) hla0 hla1).comp (tc_tendsto_left l hl a ha0 ha1)
  exact leftLim_eq_of_tendsto h

end Aux_WhittFLT_TimeReversal_revTime_comp_negRev

open Aux_WhittFLT_TimeReversal_revTime_comp_negRev in
open WhittFLT.TimeReversal in
theorem solution {S : Type*} [AddCommGroup S] [MetricSpace S] [CompleteSpace S]
    [TopologicalSpace.SeparableSpace S] (hinv : ∀ a b c : S, dist (a + c) (b + c) = dist a b)
    (x : ℝ → S) (hx : InD x) (l : ℝ → ℝ) (hl : WhittFLT.Composition.IsTimeChange 0 1 l) :
    EqOn (revTime x ∘ negRev l) (revTime (x ∘ l)) (Set.Icc 0 1) ∧
      EqOn (revTime0 x ∘ negRev l) (revTime0 (x ∘ l)) (Set.Icc 0 1) := by
  have key : EqOn (revTime x ∘ negRev l) (revTime (x ∘ l)) (Set.Icc 0 1) := by
    intro t ht
    simp only [Function.comp, negRev]
    rcases lt_or_eq_of_le ht.2 with htl | hte
    · have ha0 : 0 < 1 - t := by linarith
      have ha1 : 1 - t ≤ 1 := by linarith [ht.1]
      have hla0 : 0 < l (1 - t) := by
        have := hl.1 ⟨le_rfl, zero_le_one⟩ ⟨ha0.le, ha1⟩ ha0
        rw [tc_zero l hl] at this; exact this
      have hlt : 1 - l (1 - t) < 1 := by linarith
      unfold revTime
      rw [if_pos hlt, if_pos htl, sub_sub_cancel]
      exact (leftLim_comp x hx l hl (1 - t) ha0 ha1).symm
    · subst hte
      unfold revTime
      rw [sub_self, tc_zero l hl, sub_zero, if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
      simp [tc_zero l hl]
  refine ⟨key, ?_⟩
  intro t ht
  have := key ht
  simp only [Function.comp] at this ⊢
  unfold revTime0
  rw [this, Function.comp_apply, tc_one l hl]

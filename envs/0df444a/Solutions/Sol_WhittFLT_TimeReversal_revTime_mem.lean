-- Prove2me | solution 1 for WhittFLT.TimeReversal.revTime_mem
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T04:51:17.794009+00:00
-- url     : https://prove2.me/submissions/af26df0c-599e-4e0d-bb62-207abff37638

import Mathlib
import Definitions.Def_WhittFLT_TimeReversal_Reversal

open Set Filter Topology

namespace Aux_WhittFLT_TimeReversal_revTime_mem

open WhittFLT.TimeReversal

variable {S : Type*} [AddCommGroup S] [MetricSpace S]

lemma leftLim_tendsto (x : ℝ → S) (hx : InD x)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    Tendsto x (𝓝[<] a) (𝓝 (Function.leftLim x a)) := by
  obtain ⟨l, hl⟩ := (hx.1 a ⟨ha0.le, ha1⟩).2
  have hmem : Icc (0 : ℝ) 1 ∈ 𝓝[<] a :=
    mem_of_superset (Ioo_mem_nhdsLT ha0) (fun u hu => ⟨hu.1.le, hu.2.le.trans ha1⟩)
  have heq : 𝓝[Icc (0 : ℝ) 1 ∩ Iio a] a = 𝓝[<] a := nhdsWithin_inter_of_mem hmem
  rw [heq] at hl
  rw [leftLim_eq_of_tendsto hl]
  exact hl

lemma leftLim_right (x : ℝ → S) (hx : InD x)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Tendsto (Function.leftLim x) (𝓝[>] s) (𝓝 (x s)) := by
  have hrc := (hx.1 s ⟨hs0, hs1.le⟩).1
  rw [Metric.continuousWithinAt_iff] at hrc
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδx⟩ := hrc (ε / 2) (by linarith)
  refine ⟨min δ (1 - s), lt_min hδ (by linarith), fun {u} hu hdu => ?_⟩
  have hsu : s < u := hu
  rw [Real.dist_eq, abs_of_pos (by linarith)] at hdu
  have hu1 : u ≤ 1 := by have := min_le_right δ (1 - s); linarith
  have hlim := leftLim_tendsto x hx u (by linarith) hu1
  have hle : dist (Function.leftLim x u) (x s) ≤ ε / 2 := by
    apply le_of_tendsto (hlim.dist tendsto_const_nhds)
    filter_upwards [Ioo_mem_nhdsLT hsu] with v hv
    apply (hδx ⟨⟨by linarith [hv.1], by linarith [hv.2]⟩, hv.1.le⟩ _).le
    rw [Real.dist_eq, abs_of_pos (by linarith [hv.1])]
    have := min_le_left δ (1 - s)
    linarith [hv.2]
  linarith

lemma leftLim_left (x : ℝ → S) (hx : InD x)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    Tendsto (Function.leftLim x) (𝓝[<] a) (𝓝 (Function.leftLim x a)) := by
  have hT := leftLim_tendsto x hx a ha0 ha1
  rw [Metric.tendsto_nhdsWithin_nhds] at hT ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδx⟩ := hT (ε / 2) (by linarith)
  refine ⟨min δ a, lt_min hδ ha0, fun {u} hu hdu => ?_⟩
  have hua : u < a := hu
  rw [Real.dist_eq, abs_of_neg (by linarith)] at hdu
  have hmin1 := min_le_left δ a
  have hmin2 := min_le_right δ a
  have hu0 : 0 < u := by linarith
  have hlim := leftLim_tendsto x hx u hu0 (by linarith)
  have hlt : a - min δ a < u := by linarith
  have hle : dist (Function.leftLim x u) (Function.leftLim x a) ≤ ε / 2 := by
    apply le_of_tendsto (hlim.dist tendsto_const_nhds)
    filter_upwards [Ioo_mem_nhdsLT hlt] with v hv
    apply (hδx (show v < a by linarith [hv.2]) _).le
    rw [Real.dist_eq, abs_of_neg (by linarith [hv.2])]
    linarith [hv.1]
  linarith

lemma tendsto_one_sub_left (t : ℝ) :
    Tendsto (fun s : ℝ => 1 - s) (𝓝[<] t) (𝓝[>] (1 - t)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨((continuous_const.sub continuous_id).tendsto t).mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  show 1 - t < 1 - s
  have : s < t := hs
  linarith

lemma tendsto_one_sub_right (t : ℝ) :
    Tendsto (fun s : ℝ => 1 - s) (𝓝[>] t) (𝓝[<] (1 - t)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨((continuous_const.sub continuous_id).tendsto t).mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  show 1 - s < 1 - t
  have : t < s := hs
  linarith

lemma rev_lt (z : ℝ → S) (t : ℝ) (ht : t < 1) : revTime z t = Function.leftLim z (1 - t) := by
  unfold revTime; rw [if_pos ht]

lemma rev_one (z : ℝ → S) : revTime z 1 = z 0 := by
  unfold revTime; rw [if_neg (lt_irrefl _)]

/-- left limit of `R z` at `t ∈ (0, 1]` is `z (1 - t)`. -/
lemma rev_tendsto_left (z : ℝ → S) (hz : InD z) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    Tendsto (revTime z) (𝓝[<] t) (𝓝 (z (1 - t))) := by
  have h := (leftLim_right z hz (1 - t) (by linarith) (by linarith)).comp
    (tendsto_one_sub_left t)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have : s < t := hs
  simp only [Function.comp]
  rw [rev_lt z s (by linarith)]

lemma rev_tendsto_right (z : ℝ → S) (hz : InD z) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Tendsto (revTime z) (𝓝[>] t) (𝓝 (revTime z t)) := by
  have h := (leftLim_left z hz (1 - t) (by linarith) (by linarith)).comp
    (tendsto_one_sub_right t)
  rw [rev_lt z t ht1]
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT ht1] with s hs
  simp only [Function.comp]
  rw [rev_lt z s hs.2]

lemma rev_InD (z : ℝ → S) (hz : InD z) : InD (revTime z) := by
  refine ⟨fun t ht => ⟨?_, ?_⟩, ?_⟩
  · rcases lt_or_eq_of_le ht.2 with htl | hte
    · have h : ContinuousWithinAt (revTime z) (Ioi t) t := rev_tendsto_right z hz t ht.1 htl
      exact (continuousWithinAt_Ioi_iff_Ici.mp h).mono inter_subset_right
    · subst hte
      refine continuousWithinAt_singleton.mono ?_
      intro s hs
      exact le_antisymm hs.1.2 hs.2
  · rcases eq_or_lt_of_le ht.1 with hte | htl
    · subst hte
      refine ⟨z 0, ?_⟩
      have : Icc (0 : ℝ) 1 ∩ Iio 0 = ∅ := by
        ext s; simp only [mem_inter_iff, mem_Icc, mem_Iio, mem_empty_iff_false, iff_false]
        intro h; linarith [h.1.1, h.2]
      rw [this, nhdsWithin_empty]
      exact tendsto_bot
    · exact ⟨z (1 - t), (rev_tendsto_left z hz t htl ht.2).mono_left
        (nhdsWithin_mono _ inter_subset_right)⟩
  · have h := rev_tendsto_left z hz 1 zero_lt_one le_rfl
    rw [sub_self] at h
    rw [leftLim_eq_of_tendsto h, rev_one]

lemma rev_rev (z : ℝ → S) (hz : InD z) : EqOn (revTime (revTime z)) z (Icc 0 1) := by
  intro t ht
  rcases lt_or_eq_of_le ht.2 with htl | hte
  · rw [rev_lt _ t htl]
    have h := rev_tendsto_left z hz (1 - t) (by linarith) (by linarith [ht.1])
    rw [leftLim_eq_of_tendsto h, sub_sub_cancel]
  · subst hte
    rw [rev_one, rev_lt z 0 zero_lt_one, sub_zero, hz.2]

lemma shift_cont (hinv : ∀ a b c : S, dist (a + c) (b + c) = dist a b) (c : S) :
    Continuous (fun a : S => a - c) := by
  have : Isometry (fun a : S => a - c) := by
    apply Isometry.of_dist_eq
    intro a b
    simp only [sub_eq_add_neg]
    exact hinv a b (-c)
  exact this.continuous

lemma shift_InD (hinv : ∀ a b c : S, dist (a + c) (b + c) = dist a b) (c : S)
    (z : ℝ → S) (hz : InD z) : InD (fun s => z s - c) := by
  have hg := shift_cont hinv c
  refine ⟨fun t ht => ⟨?_, ?_⟩, ?_⟩
  · exact (hg.continuousAt).comp_continuousWithinAt (hz.1 t ht).1
  · obtain ⟨L, hL⟩ := (hz.1 t ht).2
    exact ⟨L - c, ((hg.tendsto L).comp hL)⟩
  · have h := (hg.tendsto _).comp (leftLim_tendsto z hz 1 zero_lt_one le_rfl)
    have h' : Tendsto (fun s => z s - c) (𝓝[<] 1) (𝓝 (Function.leftLim z 1 - c)) := h
    rw [leftLim_eq_of_tendsto h', hz.2]

lemma rev_shift (hinv : ∀ a b c : S, dist (a + c) (b + c) = dist a b) (c : S)
    (z : ℝ → S) (hz : InD z) :
    EqOn (revTime (fun s => z s - c)) (fun t => revTime z t - c) (Icc 0 1) := by
  have hg := shift_cont hinv c
  intro t ht
  rcases lt_or_eq_of_le ht.2 with htl | hte
  · simp only
    rw [rev_lt _ t htl, rev_lt _ t htl]
    have h := (hg.tendsto _).comp (leftLim_tendsto z hz (1 - t) (by linarith) (by linarith [ht.1]))
    have h' : Tendsto (fun s => z s - c) (𝓝[<] (1 - t))
        (𝓝 (Function.leftLim z (1 - t) - c)) := h
    exact leftLim_eq_of_tendsto h'
  · subst hte
    simp only
    rw [rev_one, rev_one]

end Aux_WhittFLT_TimeReversal_revTime_mem

open Aux_WhittFLT_TimeReversal_revTime_mem in
open WhittFLT.TimeReversal in
theorem solution {S : Type*} [AddCommGroup S] [MetricSpace S] [CompleteSpace S]
    [TopologicalSpace.SeparableSpace S] (hinv : ∀ a b c : S, dist (a + c) (b + c) = dist a b)
    (x : ℝ → S) (hx : InD x) :
    InD (revTime x) ∧ InDθ (revTime0 x) ∧
      EqOn (revTime (revTime x)) x (Set.Icc 0 1) ∧
      (x 0 = 0 → EqOn (revTime0 (revTime0 x)) x (Set.Icc 0 1)) := by
  have hR := rev_InD x hx
  have h0eq : revTime0 x = fun s => revTime x s - x 1 := rfl
  have hR0 : InD (revTime0 x) := by
    rw [h0eq]; exact shift_InD hinv (x 1) _ hR
  refine ⟨hR, ⟨hR0, ?_⟩, rev_rev x hx, ?_⟩
  · show revTime x 0 - x 1 = 0
    rw [rev_lt x 0 zero_lt_one, sub_zero, hx.2, sub_self]
  · intro hx0 t ht
    show revTime (revTime0 x) t - revTime0 x 1 = x t
    rw [h0eq, rev_shift hinv (x 1) _ hR ht]
    simp only
    rw [rev_rev x hx ht, rev_one, hx0]
    abel

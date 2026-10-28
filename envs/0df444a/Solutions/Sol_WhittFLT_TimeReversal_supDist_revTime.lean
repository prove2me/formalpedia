-- Prove2me | solution 1 for WhittFLT.TimeReversal.supDist_revTime
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T00:53:15.787544+00:00
-- url     : https://prove2.me/submissions/5dfae815-82bb-429d-9502-6dc40cb60015

import Mathlib
import Definitions.Def_WhittFLT_TimeReversal_Reversal

open Set Filter Topology

namespace Aux_WhittFLT_TimeReversal_supDist_revTime

open WhittFLT.TimeReversal

lemma leftLim_tendsto {S : Type*} [AddCommGroup S] [MetricSpace S] (x : ℝ → S) (hx : InD x)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    Tendsto x (𝓝[<] a) (𝓝 (Function.leftLim x a)) := by
  obtain ⟨l, hl⟩ := (hx.1 a ⟨ha0.le, ha1⟩).2
  have hmem : Icc (0 : ℝ) 1 ∈ 𝓝[<] a :=
    mem_of_superset (Ioo_mem_nhdsLT ha0) (fun u hu => ⟨hu.1.le, hu.2.le.trans ha1⟩)
  have heq : 𝓝[Icc (0 : ℝ) 1 ∩ Iio a] a = 𝓝[<] a := by
    exact nhdsWithin_inter_of_mem hmem
  rw [heq] at hl
  rw [leftLim_eq_of_tendsto hl]
  exact hl

lemma leftLim_right {S : Type*} [AddCommGroup S] [MetricSpace S] (x : ℝ → S) (hx : InD x)
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

end Aux_WhittFLT_TimeReversal_supDist_revTime

open Aux_WhittFLT_TimeReversal_supDist_revTime in
open WhittFLT.TimeReversal in
theorem solution {S : Type*} [AddCommGroup S] [MetricSpace S] [CompleteSpace S]
    [TopologicalSpace.SeparableSpace S] (hinv : ∀ a b c : S, dist (a + c) (b + c) = dist a b)
    (x y : ℝ → S) (hx : InD x) (hy : InD y) :
    WhittFLT.Composition.supDist 0 1 (revTime x) (revTime y) = WhittFLT.Composition.supDist 0 1 x y ∧
      WhittFLT.Composition.supDist 0 1 (revTime0 x) (revTime0 y) ≤
        WhittFLT.Composition.supDist 0 1 x y + edist (x 1) (y 1) ∧
      WhittFLT.Composition.supDist 0 1 (revTime0 x) (revTime0 y) ≤ 2 * WhittFLT.Composition.supDist 0 1 x y := by
  have hrev_lt : ∀ (z : ℝ → S) t, t < 1 → revTime z t = Function.leftLim z (1 - t) :=
    fun z t ht => by unfold revTime; rw [if_pos ht]
  have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have part1 : WhittFLT.Composition.supDist 0 1 (revTime x) (revTime y) =
      WhittFLT.Composition.supDist 0 1 x y := by
    unfold WhittFLT.Composition.supDist
    apply le_antisymm
    · apply iSup₂_le
      intro t ht
      rcases lt_or_eq_of_le ht.2 with htl | hte
      · rw [hrev_lt x t htl, hrev_lt y t htl]
        have ha0 : 0 < 1 - t := by linarith
        have ha1 : 1 - t ≤ 1 := by linarith [ht.1]
        have hT := (leftLim_tendsto x hx _ ha0 ha1).edist (leftLim_tendsto y hy _ ha0 ha1)
        apply le_of_tendsto hT
        filter_upwards [Ioo_mem_nhdsLT ha0] with u hu
        exact le_iSup₂ (f := fun t (_ : t ∈ Icc (0 : ℝ) 1) => edist (x t) (y t)) u
          ⟨hu.1.le, by linarith [hu.2]⟩
      · subst hte
        unfold revTime
        rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
        exact le_iSup₂ (f := fun t (_ : t ∈ Icc (0 : ℝ) 1) => edist (x t) (y t)) 0 h0mem
    · apply iSup₂_le
      intro s hs
      rcases lt_or_eq_of_le hs.2 with hsl | hse
      · have hT := (leftLim_right x hx s hs.1 hsl).edist (leftLim_right y hy s hs.1 hsl)
        apply le_of_tendsto hT
        filter_upwards [Ioo_mem_nhdsGT hsl] with u hu
        have hlt : 1 - u < 1 := by linarith [hu.1, hs.1]
        have e1 := hrev_lt x (1 - u) hlt
        have e2 := hrev_lt y (1 - u) hlt
        rw [sub_sub_cancel] at e1 e2
        rw [← e1, ← e2]
        exact le_iSup₂ (f := fun t (_ : t ∈ Icc (0 : ℝ) 1) => edist (revTime x t) (revTime y t))
          (1 - u) ⟨by linarith [hu.2], by linarith [hu.1, hs.1]⟩
      · subst hse
        have e1 : revTime x 0 = x 1 := by rw [hrev_lt x 0 zero_lt_one, sub_zero, hx.2]
        have e2 : revTime y 0 = y 1 := by rw [hrev_lt y 0 zero_lt_one, sub_zero, hy.2]
        rw [← e1, ← e2]
        exact le_iSup₂ (f := fun t (_ : t ∈ Icc (0 : ℝ) 1) => edist (revTime x t) (revTime y t))
          0 h0mem
  have hpt : ∀ a b c d : S, edist (a - c) (b - d) ≤ edist a b + edist c d := by
    intro a b c d
    rw [edist_dist, edist_dist, edist_dist,
      ← ENNReal.ofReal_add dist_nonneg dist_nonneg]
    apply ENNReal.ofReal_le_ofReal
    have h1 : dist (a - c) (b - c) = dist a b := by
      rw [sub_eq_add_neg, sub_eq_add_neg]; exact hinv a b (-c)
    have h2 : dist (b - c) (b - d) = dist c d := by
      rw [show b - c = -c + b by abel, show b - d = -d + b by abel, hinv]
      have h3 := hinv (-c) (-d) (c + d)
      rw [show -c + (c + d) = d by abel, show -d + (c + d) = c by abel] at h3
      rw [← h3, dist_comm]
    calc dist (a - c) (b - d) ≤ dist (a - c) (b - c) + dist (b - c) (b - d) := dist_triangle _ _ _
      _ = dist a b + dist c d := by rw [h1, h2]
  have part2 : WhittFLT.Composition.supDist 0 1 (revTime0 x) (revTime0 y) ≤
      WhittFLT.Composition.supDist 0 1 x y + edist (x 1) (y 1) := by
    rw [← part1]
    unfold WhittFLT.Composition.supDist
    apply iSup₂_le
    intro t ht
    unfold revTime0
    refine (hpt _ _ _ _).trans (add_le_add ?_ le_rfl)
    exact le_iSup₂ (f := fun t (_ : t ∈ Icc (0 : ℝ) 1) => edist (revTime x t) (revTime y t)) t ht
  refine ⟨part1, part2, part2.trans ?_⟩
  rw [two_mul]
  apply add_le_add le_rfl
  unfold WhittFLT.Composition.supDist
  exact le_iSup₂ (f := fun t (_ : t ∈ Icc (0 : ℝ) 1) => edist (x t) (y t)) 1 h1mem

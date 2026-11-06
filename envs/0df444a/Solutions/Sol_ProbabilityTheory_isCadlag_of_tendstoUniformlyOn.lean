-- Prove2me | solution 1 for ProbabilityTheory.isCadlag_of_tendstoUniformlyOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:13:34.778953+00:00
-- url     : https://prove2.me/submissions/62542ea3-ff87-41da-a1f8-a010c4095492

import Definitions.Def_LeanLevy_Processes_Cadlag
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Filter Set Topology ProbabilityTheory
open scoped NNReal

theorem solution {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ n, IsCadlag (F n)) (h : ∀ T : ℝ, TendstoUniformlyOn F f atTop (Set.Iic T)) :
    IsCadlag f := by
  intro t
  have hunif : ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ Set.Iic (t + 1), dist (f x) (F n x) < ε :=
    fun ε hε => (Metric.tendstoUniformlyOn_iff.mp (h (t + 1))) ε hε
  constructor
  · -- Right-continuity at `t`.
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := (hunif (ε / 3) (by positivity)).exists
    obtain ⟨δ', hδ'pos, hδ'⟩ :=
      Metric.continuousWithinAt_iff.mp (hF n t).1 (ε / 3) (by positivity)
    refine ⟨min δ' 1, lt_min hδ'pos one_pos, ?_⟩
    intro s hs hsdist
    have hsd' : dist s t < δ' := lt_of_lt_of_le hsdist (min_le_left _ _)
    have hs1 : s ∈ Set.Iic (t + 1) := by
      have hlt1 : dist s t < 1 := lt_of_lt_of_le hsdist (min_le_right _ _)
      rw [Real.dist_eq, abs_lt] at hlt1
      simp only [Set.mem_Iic]; linarith [hlt1.2]
    have ht1 : t ∈ Set.Iic (t + 1) := by simp
    have T : dist (f s) (f t) ≤
        dist (f s) (F n s) + dist (F n s) (F n t) + dist (F n t) (f t) := dist_triangle4 _ _ _ _
    have B1 : dist (f s) (F n s) < ε / 3 := hn s hs1
    have B2 : dist (F n s) (F n t) < ε / 3 := hδ' hs hsd'
    have B3 : dist (F n t) (f t) < ε / 3 := by rw [dist_comm]; exact hn t ht1
    linarith [T, B1, B2, B3]
  · -- Existence of the left limit at `t`.
    choose l hl using fun n => (hF n t).2
    have hcauchy : CauchySeq l := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hunif (ε / 4) (by positivity))
      refine ⟨N, fun m hm n hn => ?_⟩
      obtain ⟨δm, hδmpos, hδm⟩ :=
        Metric.tendsto_nhdsWithin_nhds.mp (hl m) (ε / 4) (by positivity)
      obtain ⟨δn, hδnpos, hδn⟩ :=
        Metric.tendsto_nhdsWithin_nhds.mp (hl n) (ε / 4) (by positivity)
      set δ := min δm δn with hδdef
      have hδpos : 0 < δ := lt_min hδmpos hδnpos
      set s := t - δ / 2 with hsdef
      have hslt : s ∈ Set.Iio t := by
        simp only [Set.mem_Iio, hsdef]; linarith
      have hsdist : dist s t < δ := by
        rw [Real.dist_eq, hsdef, abs_of_nonpos (by linarith)]; linarith
      have hs1 : s ∈ Set.Iic (t + 1) := by
        simp only [Set.mem_Iic, hsdef]; linarith
      have hb1 : dist (l m) (F m s) < ε / 4 := by
        rw [dist_comm]; exact hδm hslt (lt_of_lt_of_le hsdist (min_le_left _ _))
      have hb2 : dist (F m s) (f s) < ε / 4 := by
        rw [dist_comm]; exact hN m hm s hs1
      have hb3 : dist (f s) (F n s) < ε / 4 := hN n hn s hs1
      have hb4 : dist (F n s) (l n) < ε / 4 := hδn hslt (lt_of_lt_of_le hsdist (min_le_right _ _))
      have T1 : dist (l m) (l n) ≤ dist (l m) (f s) + dist (f s) (l n) := dist_triangle _ _ _
      have T2 : dist (l m) (f s) ≤ dist (l m) (F m s) + dist (F m s) (f s) := dist_triangle _ _ _
      have T3 : dist (f s) (l n) ≤ dist (f s) (F n s) + dist (F n s) (l n) := dist_triangle _ _ _
      linarith [T1, T2, T3, hb1, hb2, hb3, hb4]
    obtain ⟨L, hLtend⟩ := cauchySeq_tendsto_of_complete hcauchy
    refine ⟨L, ?_⟩
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    have hLev : ∀ᶠ n in atTop, dist (l n) L < ε / 3 :=
      Metric.tendsto_nhds.mp hLtend (ε / 3) (by positivity)
    obtain ⟨n, hnU, hnL⟩ := ((hunif (ε / 3) (by positivity)).and hLev).exists
    obtain ⟨δ, hδpos, hδ⟩ := Metric.tendsto_nhdsWithin_nhds.mp (hl n) (ε / 3) (by positivity)
    refine ⟨δ, hδpos, ?_⟩
    intro s hs hsdist
    have hs1 : s ∈ Set.Iic (t + 1) := by
      simp only [Set.mem_Iio] at hs
      simp only [Set.mem_Iic]; linarith
    have T : dist (f s) L ≤
        dist (f s) (F n s) + dist (F n s) (l n) + dist (l n) L := dist_triangle4 _ _ _ _
    have B1 : dist (f s) (F n s) < ε / 3 := hnU s hs1
    have B2 : dist (F n s) (l n) < ε / 3 := hδ hs hsdist
    have B3 : dist (l n) L < ε / 3 := hnL
    linarith [T, B1, B2, B3]


-- Prove2me | solution 1 for StochApproxDyn.Lyapunov.eq_sublevel_of_not_mem_image
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:22:07.507192+00:00
-- url     : https://prove2.me/submissions/9c6713cc-9c7c-499e-bf1f-07e6939e7abb

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_ChainRecurrence
import Definitions.Def_StochApproxDyn_Lyapunov_LyapunovFunction

open scoped NNReal

set_option autoImplicit false

open StochApproxDyn.Lyapunov NNReal in
theorem solution {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M)
    (Λ : Set M) (V : M → ℝ) (hV : IsLyapunovFunction Φ Λ V)
    (L : Set M) (hL : StochApproxDyn.LimitSet.IsInternallyChainTransitive Φ L)
    (vstar : ℝ) (hvstar : IsGLB (V '' L) vstar)
    (c : ℝ) (hcΛ : c ∉ V '' Λ) (hc : vstar < c) :
    L = {x ∈ L | V x < c} := by
  classical
  obtain ⟨_, _, hVc, hVΛ, hVanti⟩ := hV
  obtain ⟨_, hLc, hinv, hchain⟩ := hL
  have hmono : ∀ x (t : ℝ≥0), V (Φ t x) ≤ V x := by
    intro x t
    by_cases hx : x ∈ Λ
    · rw [hVΛ x hx t]
    · have := (hVanti x hx).antitone (zero_le (a := t))
      simpa [Flow.map_zero_apply] using this
  have hstrict : ∀ x, V x = c → ∀ t : ℝ≥0, 0 < t → V (Φ t x) < c := by
    intro x hx t ht
    have hxΛ : x ∉ Λ := fun h => hcΛ ⟨x, h, hx⟩
    have := hVanti x hxΛ ht
    simpa [Flow.map_zero_apply, hx] using this
  obtain ⟨_, ⟨a, haL, rfl⟩, -, hac⟩ := hvstar.exists_between hc
  have hAc : IsCompact (L ∩ {x | V x ≤ c}) :=
    hLc.inter_right (isClosed_le hVc continuous_const)
  have hg : Continuous fun x => V (Φ 1 x) :=
    hVc.comp (Φ.continuous continuous_const continuous_id)
  obtain ⟨x0, hx0A, hx0max⟩ := hAc.exists_isMaxOn ⟨a, haL, hac.le⟩ hg.continuousOn
  have hx0lt : V (Φ 1 x0) < c := by
    rcases lt_or_eq_of_le (show V x0 ≤ c from hx0A.2) with h | h
    · exact lt_of_le_of_lt (hmono x0 1) h
    · exact hstrict x0 h 1 one_pos
  set η := min (c - V (Φ 1 x0)) (c - V a) with hηdef
  have hη : 0 < η := lt_min (by linarith) (by linarith)
  have hη1 : η ≤ c - V (Φ 1 x0) := min_le_left _ _
  have hη2 : η ≤ c - V a := min_le_right _ _
  have hstep : ∀ x ∈ L, V x ≤ c → ∀ t : ℝ≥0, 1 ≤ t → V (Φ t x) ≤ c - η := by
    intro x hxL hxc t ht
    have h1 : Φ t x = Φ (t - 1) (Φ 1 x) := by
      rw [← Flow.map_add, tsub_add_cancel_of_le ht]
    have h2 : V (Φ 1 x) ≤ V (Φ 1 x0) := hx0max ⟨hxL, hxc⟩
    have h3 := hmono (Φ 1 x) (t - 1)
    rw [h1]
    linarith
  obtain ⟨δ, hδ, hδV⟩ := Metric.uniformContinuousOn_iff.1
    (hLc.uniformContinuousOn_of_continuous hVc.continuousOn) η hη
  ext b
  constructor
  · intro hbL
    refine ⟨hbL, ?_⟩
    obtain ⟨k, y, t, -, hT, h0, hj, hyk⟩ := hchain ⟨a, haL⟩ ⟨b, hbL⟩ δ hδ 1 one_pos
    have key : ∀ j, j ≤ k → V (y j : M) < c := by
      intro j
      induction j with
      | zero =>
        intro _
        have h0' : dist (y 0 : M) a < δ := h0
        have hd := hδV (y 0 : M) (y 0).2 a haL h0'
        rw [Real.dist_eq] at hd
        have := (abs_lt.1 hd).2
        linarith
      | succ j ih =>
        intro hj1
        have hyj := ih (by omega)
        have hd : dist (Φ (t j) (y j : M)) (y (j + 1) : M) < δ := hj j (by omega)
        have hmem : Φ (t j) (y j : M) ∈ L :=
          (StochApproxDyn.LimitSet.restrictSemiflow Φ hinv (t j) (y j)).2
        have hd2 := hδV _ hmem (y (j + 1) : M) (y (j + 1)).2 hd
        rw [Real.dist_eq] at hd2
        have h4 := (abs_lt.1 hd2).1
        have h5 := hstep (y j : M) (y j).2 hyj.le (t j) (hT j (by omega))
        linarith
    have := key k le_rfl
    rw [hyk] at this
    exact this
  · exact fun h => h.1

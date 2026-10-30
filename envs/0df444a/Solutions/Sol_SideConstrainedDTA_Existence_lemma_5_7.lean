-- Prove2me | solution 1 for SideConstrainedDTA.Existence.lemma_5_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T23:35:34.849319+00:00
-- url     : https://prove2.me/submissions/55439178-a47f-413e-aebd-fc2fefbac793

import Mathlib
import Definitions.Def_SideConstrainedDTA_Existence_Setting

open MeasureTheory Set Filter Topology

open SideConstrainedDTA.Existence

theorem solution {I W E : Type*} [Fintype I] [Fintype W] [DecidableEq I] [DecidableEq W]
    (N : Model I W E) (hN : N.Basic) (Φ : (W → ℝ → ℝ) → W → ℝ → ℝ)
    (S : (W → ℝ → ℝ) → Prop) (A : Corr W) (M : ℝ)
    (hM : ∀ h, S h → ∀ t ∈ Icc N.t0 N.tf, ∀ p, (admDev N A h p t).Nonempty →
      ∃ x ∈ admDev N A h p t, Φ h x.1 (t + x.2) < M) (hs : W → ℝ → ℝ) :
    IsSCDE N Φ S A hs ↔ IsSCDE N (PsiTrunc Φ M) S A hs := by
  constructor
  · rintro ⟨hS, hE⟩
    exact ⟨hS, fun p t ht x hx => min_le_min (hE p t ht x hx) le_rfl⟩
  · rintro ⟨hS, hE⟩
    refine ⟨hS, fun p t ht x hx => ?_⟩
    obtain ⟨y, hy, hyM⟩ := hM hs hS t ht p ⟨x, hx⟩
    have h1 := hE p t ht y hy
    have h2 := hE p t ht x hx
    simp only [PsiTrunc] at h1 h2
    have hy' : min (Φ hs y.1 (t + y.2)) M = Φ hs y.1 (t + y.2) := min_eq_left hyM.le
    rw [hy'] at h1
    have hp : Φ hs p t < M := by
      rcases min_le_iff.1 (le_of_eq rfl : min (Φ hs p t) M ≤ min (Φ hs p t) M) with h | h
      · by_contra hc
        push Not at hc
        have : min (Φ hs p t) M = M := min_eq_right hc
        linarith
      · by_contra hc
        push Not at hc
        have : min (Φ hs p t) M = M := min_eq_right hc
        linarith
    rw [min_eq_left hp.le] at h2
    exact h2.trans (min_le_left _ _)

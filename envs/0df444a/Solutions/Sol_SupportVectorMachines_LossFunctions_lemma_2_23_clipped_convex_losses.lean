-- Prove2me | solution 1 for SupportVectorMachines.LossFunctions.lemma_2_23_clipped_convex_losses
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:08:37.820314+00:00
-- url     : https://prove2.me/submissions/6bbd8a3b-b59a-4ded-8689-06008d4d6337

import Mathlib
import Definitions.Def_SupportVectorMachines_LossFunctions_RiskBasics
import Definitions.Def_SupportVectorMachines_LossFunctions_ClassificationLosses

namespace SupportVectorMachines.LossFunctions

theorem aux_l223_clip_mem (M t : ℝ) (hM : 0 < M) : clip M t ∈ Set.Icc (-M) M := by
  unfold clip
  split_ifs with h1 h2
  · exact ⟨le_refl _, by linarith⟩
  · exact ⟨by linarith, le_refl _⟩
  · exact ⟨not_lt.mp h1, not_lt.mp h2⟩

theorem aux_l223_fwd (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) (M : ℝ) (hM : 0 < M)
    (hc : ∀ t, f (clip M t) ≤ f t) : ∃ t0 ∈ Set.Icc (-M) M, ∀ t, f t0 ≤ f t := by
  have hcont : Continuous f := hf.locallyLipschitz.continuous
  obtain ⟨t0, ht0, hmin⟩ := (isCompact_Icc (a := -M) (b := M)).exists_isMinOn
    (Set.nonempty_Icc.mpr (by linarith)) hcont.continuousOn
  refine ⟨t0, ht0, fun t => ?_⟩
  exact le_trans (hmin (aux_l223_clip_mem M t hM)) (hc t)

theorem aux_l223_bwd (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) (M : ℝ)
    (t0 : ℝ) (ht0 : t0 ∈ Set.Icc (-M) M) (hmin : ∀ t, f t0 ≤ f t) (t : ℝ) :
    f (clip M t) ≤ f t := by
  obtain ⟨h1, h2⟩ := ht0
  unfold clip
  split_ifs with ha hb
  · -- t < -M ≤ t0, so -M ∈ [t, t0]
    have hz : -M ∈ segment ℝ t t0 := by
      rw [segment_eq_Icc (by linarith)]
      exact ⟨by linarith, h1⟩
    have := hf.le_on_segment (Set.mem_univ t) (Set.mem_univ t0) hz
    have h := hmin t
    rw [max_eq_left h] at this
    exact this
  · -- t0 ≤ M < t
    have hz : M ∈ segment ℝ t0 t := by
      rw [segment_eq_Icc (by linarith)]
      exact ⟨h2, by linarith⟩
    have := hf.le_on_segment (Set.mem_univ t0) (Set.mem_univ t) hz
    have h := hmin t
    rw [max_eq_right h] at this
    exact this
  · exact le_refl _

end SupportVectorMachines.LossFunctions

open SupportVectorMachines.LossFunctions

theorem solution {X : Type*} (L : Loss X)
    (hconv : ∀ x y, ConvexOn ℝ Set.univ (L x y)) (M : ℝ) (hM : 0 < M) :
    CanBeClipped L M ↔ ∀ x y, ∃ t0 ∈ Set.Icc (-M) M, ∀ t, L x y t0 ≤ L x y t := by
  constructor
  · intro hc x y
    exact aux_l223_fwd (L x y) (hconv x y) M hM (fun t => hc x y t)
  · intro h x y t
    obtain ⟨t0, ht0, hmin⟩ := h x y
    exact aux_l223_bwd (L x y) (hconv x y) M t0 ht0 hmin t

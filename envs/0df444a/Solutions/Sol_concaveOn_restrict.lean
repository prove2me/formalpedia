-- Prove2me | solution 1 for concaveOn_restrict
-- status  : ACCEPTED   (disprove)
-- author  : @vebis
-- created : 2026-10-21T17:16:24.40467+00:00
-- url     : https://prove2.me/submissions/a12dd790-2350-4656-bc18-f216c32cd457

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ {g : ℝ → ℝ} {s t : Set ℝ} (hst : t ⊆ s) (hconc : ConcaveOn ℝ s g), ConcaveOn ℝ t g) := by
  intro h
  have h0 : ConcaveOn ℝ (Set.univ : Set ℝ) (fun _ : ℝ => (0 : ℝ)) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ _
    simp
  have h1 := h (g := fun _ : ℝ => (0 : ℝ)) (s := Set.univ) (t := {0, 1}) (Set.subset_univ _) h0
  have hc := h1.1
  have h01 : ((1 : ℝ) / 2) • (0 : ℝ) + ((1 : ℝ) / 2) • (1 : ℝ) ∈ ({0, 1} : Set ℝ) :=
    hc (by simp) (by simp) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h01

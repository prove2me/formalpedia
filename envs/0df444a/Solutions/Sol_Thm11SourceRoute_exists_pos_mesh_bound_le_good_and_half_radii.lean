-- Prove2me | solution 1 for Thm11SourceRoute.exists_pos_mesh_bound_le_good_and_half_radii
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:23:18.267297+00:00
-- url     : https://prove2.me/submissions/16934e5d-694e-4d80-838f-a47763b61a1c

import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

theorem solution
    (S : Finset ℝ) (rho : ℝ → ℝ) {δgood : ℝ}
    (hδgood : 0 < δgood)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δgood ∧
      ∀ c : ℝ, c ∈ S → δ ≤ rho c / 2 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨δgood, hδgood, le_refl _, by simp⟩
  | insert a S ha ih =>
    obtain ⟨δ, hδ, hδg, hδS⟩ := ih (fun c hc => hrho_pos c (Finset.mem_insert_of_mem hc))
    have hra : 0 < rho a := hrho_pos a (Finset.mem_insert_self a S)
    refine ⟨min δ (rho a / 2), lt_min hδ (by linarith), le_trans (min_le_left _ _) hδg, ?_⟩
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact min_le_right _ _
    · exact le_trans (min_le_left _ _) (hδS c hc)

-- Prove2me | solution 1 for Thm11SourceRoute.exists_pos_abs_bound_on_Icc_of_bddAbove_bddBelow
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:23:18.8911+00:00
-- url     : https://prove2.me/submissions/89c616e9-e2a9-4a96-a5d3-78d66b8a145b

import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

theorem solution {f : ℝ → ℝ} {a b : ℝ}
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ C := by
  obtain ⟨M, hM⟩ := hAbove
  obtain ⟨m, hm⟩ := hBelow
  refine ⟨|M| + |m| + 1, by positivity, ?_⟩
  intro x hx
  have h1 : f x ≤ M := hM (Set.mem_image_of_mem f hx)
  have h2 : m ≤ f x := hm (Set.mem_image_of_mem f hx)
  rw [abs_le]
  constructor
  · linarith [neg_abs_le m, abs_nonneg M]
  · linarith [le_abs_self M, abs_nonneg m]

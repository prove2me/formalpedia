-- Prove2me | solution 1 for WilliamsonShmoys.triangulation_completion_face_count_6e15fe35
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:57:48.625508+00:00
-- url     : https://prove2.me/submissions/6c083e37-0771-4096-a6b6-c0a58632e36c

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_triangulation_completion_face_count_6e15fe35

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → M = N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = M.edgeSet.ncard + 2 ∧
      3 * f = 2 * M.edgeSet.ncard := by
  have hEdges :=
    WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_completion_face_count_6e15fe35
      M hM hMax hCard
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega
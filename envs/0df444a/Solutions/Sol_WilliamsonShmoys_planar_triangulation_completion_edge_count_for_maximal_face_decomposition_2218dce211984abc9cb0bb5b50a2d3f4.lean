-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion_edge_count_for_maximal_face_decomposition_2218dce211984abc9cb0bb5b50a2d3f4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:12:53.327934+00:00
-- url     : https://prove2.me/submissions/3c0136ff-92f1-48d1-a5cc-e0de12852e2e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_finite_maximal_extension_f15616f1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_f15616f1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hKH, hH, hMax⟩ :=
    WilliamsonShmoys.planar_drawingOn_finite_maximal_extension_f15616f1 K hK
  exact ⟨H, hKH, hH,
    WilliamsonShmoys.maximal_drawable_graph_edge_count_f15616f1 H hH hCard hMax⟩
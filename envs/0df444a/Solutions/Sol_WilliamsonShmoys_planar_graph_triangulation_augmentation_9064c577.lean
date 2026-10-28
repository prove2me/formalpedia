-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_triangulation_augmentation_9064c577
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:21:39.493961+00:00
-- url     : https://prove2.me/submissions/71759025-6eae-4b8f-aa80-7d96b21bfc83
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_exists_maximal_9064c577_retry2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count_9064c577_retry3

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hConn : H.Connected)
    (hDraw : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hKDraw, hMax⟩ :=
    WilliamsonShmoys.planar_supergraph_exists_maximal_9064c577_retry2 H hDraw
  refine ⟨K, hHK, hKDraw, ?_⟩
  exact WilliamsonShmoys.maximal_planar_supergraph_edge_count_9064c577_retry3
    K hKDraw hMax hCard
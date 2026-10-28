-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:06:06.060955+00:00
-- url     : https://prove2.me/submissions/81775d1b-fa6c-4d74-8b3a-2246c6523f4b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_for_exact_edge_count_completion
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_exact_edge_count_for_completion

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨K, hNK, hK, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph_for_exact_edge_count_completion N hN hCard
  exact ⟨K, hNK, hK,
    WilliamsonShmoys.maximal_drawable_graph_exact_edge_count_for_completion K hK hCard hMax⟩
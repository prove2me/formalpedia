-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_extension_for_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:51:53.487657+00:00
-- url     : https://prove2.me/submissions/5e3dd43e-301c-4cb9-806d-7e05d9a555de
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_6230202c_e2d1_4f54_a7eb_9eadc154ee57
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_graph_6230202c_e2d1_4f54_a7eb_9eadc154ee57

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, G ≤ L ∧ HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hGL, hL, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_6230202c_e2d1_4f54_a7eb_9eadc154ee57
      G hG hCard
  exact ⟨L, hGL, hL,
    WilliamsonShmoys.edge_count_of_maximal_planar_graph_6230202c_e2d1_4f54_a7eb_9eadc154ee57
      L hL hCard hmax⟩
-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_triangulation_completion_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:47:50.439969+00:00
-- url     : https://prove2.me/submissions/c5763899-f2d8-422e-a846-2bc453c40d67
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph_d8e86b30_fed1_4ee5_9c6d_8ff76555c4e7
import Theorems.Thm_WilliamsonShmoys_edge_count_of_edge_maximal_planar_graph_d8e86b30_fed1_4ee5_9c6d_8ff76555c4e7

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQdraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ R : SimpleGraph V, Q ≤ R ∧
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      3 * Fintype.card V = R.edgeSet.ncard + 6 := by
  obtain ⟨R, hQR, hRdraw, hRmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph_d8e86b30_fed1_4ee5_9c6d_8ff76555c4e7
      Q hQdraw
  exact ⟨R, hQR, hRdraw,
    WilliamsonShmoys.edge_count_of_edge_maximal_planar_graph_d8e86b30_fed1_4ee5_9c6d_8ff76555c4e7
      R hRdraw hCard hRmax⟩
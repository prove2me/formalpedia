-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_triangulation_edge_count_93a36477_a46b_4b11_b4cb_7379952edbbc
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:57:02.769424+00:00
-- url     : https://prove2.me/submissions/6814584d-7f85-4c35-8116-64ae12695567
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_supergraph_93a36477_a46b_4b11_b4cb_7379952edbbc

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    Exists fun M : SimpleGraph V => L <= M /\ WilliamsonShmoys.HasPlanarDrawingOn M /\
      3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  classical
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.planar_drawable_maximal_supergraph L hL
  exact ⟨M, hLM, hM,
    WilliamsonShmoys.maximal_planar_edge_count_for_supergraph_93a36477_a46b_4b11_b4cb_7379952edbbc
      M hV hM hmax⟩
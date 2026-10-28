-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_supergraph_triangulation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:16:06.741999+00:00
-- url     : https://prove2.me/submissions/73c56d5a-a042-4858-8a2b-6b134a2c7cf7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_triangulation_2a27a388_e06b_4db0_bfe8_7a93ec4c9c7f_exists_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_triangulation_2a27a388_e06b_4db0_bfe8_7a93ec4c9c7f_maximal_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    Exists (fun K : SimpleGraph V =>
      And (H <= K) (And (WilliamsonShmoys.HasPlanarDrawingOn K)
        (K.edgeSet.ncard + 6 = 3 * Fintype.card V))) := by
  refine Exists.elim
    (WilliamsonShmoys.triangulation_2a27a388_e06b_4db0_bfe8_7a93ec4c9c7f_exists_maximal_supergraph H hH) ?_
  intro K h
  exact Exists.intro K (And.intro h.left (And.intro h.right.left
    (WilliamsonShmoys.triangulation_2a27a388_e06b_4db0_bfe8_7a93ec4c9c7f_maximal_edge_count K hV h.right.left h.right.right)))
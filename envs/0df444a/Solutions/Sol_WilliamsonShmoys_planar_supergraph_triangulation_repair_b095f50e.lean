-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_triangulation_repair_b095f50e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:23:42.659991+00:00
-- url     : https://prove2.me/submissions/a4cb7b7c-5231-4286-81c0-2d815d00f97c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_drawable_supergraph_repair_20261027
import Theorems.Thm_WilliamsonShmoys_edge_maximal_drawable_supergraph_card_repair_20261027

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ U : SimpleGraph V,
      W ≤ U ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      U.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨U, hWU, hU, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_drawable_supergraph_repair_20261027 W hW
  exact ⟨U, hWU, hU,
    WilliamsonShmoys.edge_maximal_drawable_supergraph_card_repair_20261027
      W hV U hWU hU hmax⟩
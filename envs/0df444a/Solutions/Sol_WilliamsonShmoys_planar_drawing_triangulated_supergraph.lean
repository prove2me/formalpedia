-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulated_supergraph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:25:24.580247+00:00
-- url     : https://prove2.me/submissions/44872233-48d9-4c93-a131-91986ae5c4b9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_supergraph_repair_543ac5d4
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_repair_543ac5d4

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S) :
    ∃ T : SimpleGraph V,
      S <= T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
        3 * Fintype.card V = T.edgeSet.ncard + 6 := by
  obtain ⟨T, hST, hT, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_supergraph_repair_543ac5d4 S hS
  exact ⟨T, hST, hT,
    WilliamsonShmoys.maximal_planar_edge_count_repair_543ac5d4 T hV hT hmax⟩
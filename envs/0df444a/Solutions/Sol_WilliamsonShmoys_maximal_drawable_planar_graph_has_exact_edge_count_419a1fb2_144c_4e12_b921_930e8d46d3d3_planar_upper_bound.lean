-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_planar_graph_has_exact_edge_count_419a1fb2_144c_4e12_b921_930e8d46d3d3_planar_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:33:08.499791+00:00
-- url     : https://prove2.me/submissions/82706fca-ad0f-4991-97c7-20898bccf713
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph_for_419a1fb2_144c_4e12_b921_930e8d46d3d3_planar_upper_bound

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hKH, hPlanar, hCardEdges, hTriangulated⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulated_supergraph_for_419a1fb2_144c_4e12_b921_930e8d46d3d3_planar_upper_bound
      K hK hCard
  omega
-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_23341804_e9bd_4849_9be7_9e709bd142a9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:51:36.702355+00:00
-- url     : https://prove2.me/submissions/05a43ad0-9df3-4018-8c9e-53347a5b30d6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_1591b9cd_ac13_4639_82d2_61e7ddbdd660
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_1591b9cd_ac13_4639_82d2_61e7ddbdd660

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hKH, hDraw, hMax, hEdges⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_1591b9cd_ac13_4639_82d2_61e7ddbdd660 K hK hCard
  have hCount := WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_1591b9cd_ac13_4639_82d2_61e7ddbdd660 H hDraw hMax hCard
  omega
-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_edge_bound_connected_bf226c5d
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:53:57.52251+00:00
-- url     : https://prove2.me/submissions/d35dd0ea-d51f-42ab-b96b-91a11ab7dab6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_88c6cb28_d980_4ba8_aca2_3c8dda9dfd09
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_88c6cb28_d980_4ba8_aca2_3c8dda9dfd09

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConnected : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHPlanar, hHMaximal⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_88c6cb28_d980_4ba8_aca2_3c8dda9dfd09 G hV hG
  have hEdge : G.edgeSet.ncard ≤ H.edgeSet.ncard :=
    Set.ncard_mono (SimpleGraph.edgeSet_mono hGH)
  have hBound := WilliamsonShmoys.maximal_planar_edge_bound_88c6cb28_d980_4ba8_aca2_3c8dda9dfd09 H hV hHPlanar hHMaximal
  omega
-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_bound__p2m_37c28fdb_a658_40e3_b030_60d915d37051_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:14:52.975207+00:00
-- url     : https://prove2.me/submissions/51f87251-2f55-4631-9af2-ed6c21173b90
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_edge_count__p2m_0268dd7c_b22a_4ecf_a4e7_1329a8208a94_a1
import Theorems.Thm_WilliamsonShmoys_planar_connectivity_augmentation__p2m_0268dd7c_b22a_4ecf_a4e7_1329a8208a94_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_subgraph_mono__p2m_0268dd7c_b22a_4ecf_a4e7_1329a8208a94_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHconn, hHplanar⟩ :=
    WilliamsonShmoys.planar_connectivity_augmentation__p2m_0268dd7c_b22a_4ecf_a4e7_1329a8208a94_a1 G hG
  have hH := WilliamsonShmoys.planar_connected_edge_count__p2m_0268dd7c_b22a_4ecf_a4e7_1329a8208a94_a1 H hHplanar hHconn hV
  exact WilliamsonShmoys.planar_edge_count_subgraph_mono__p2m_0268dd7c_b22a_4ecf_a4e7_1329a8208a94_a1 G H hGH hH
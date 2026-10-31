-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_le__p2m_bd86803d_f791_454d_9e3d_cf8ce9ce0da0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T13:10:24.704434+00:00
-- url     : https://prove2.me/submissions/9702ac3f-bece-42a0-9460-4f4e4224a34b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_bound__p2m_665380ce_9fb5_4c8b_8ba0_a10e16d5f767_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHplanar, hHcard⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_edge_bound__p2m_665380ce_9fb5_4c8b_8ba0_a10e16d5f767_a1
      G hG hV
  have hcard : G.edgeSet.ncard ≤ H.edgeSet.ncard :=
    Set.ncard_mono hGH
  omega
-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_1cedfa43_e759_4304_8f59_175ee0ad0ade_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:11:51.652689+00:00
-- url     : https://prove2.me/submissions/101a5e6c-ca3e-4ca6-a771-8d13c96adc48
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_aa8f027a_93b4_4926_a309_4c6509e6e203_a2
import Theorems.Thm_WilliamsonShmoys_connect_planar_components__p2m_aa8f027a_93b4_4926_a309_4c6509e6e203_a2

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hEdges, hConnected, hDrawH⟩ :=
    WilliamsonShmoys.connect_planar_components__p2m_aa8f027a_93b4_4926_a309_4c6509e6e203_a2
      L hDraw hV
  exact le_trans hEdges
    (WilliamsonShmoys.connected_planar_edge_bound__p2m_aa8f027a_93b4_4926_a309_4c6509e6e203_a2
      H hConnected hDrawH hV)
-- Prove2me | solution 1 for WilliamsonShmoys.simple_planar_edge_bound__p2m_034f5ef2_6768_4eb9_83c3_8c1c8d5ce02b_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:56:55.160137+00:00
-- url     : https://prove2.me/submissions/935b7ccc-3d05-4d0c-b81f-34520b163151
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_f0f39874_5ae5_48cf_ae7d_0d6801141c64_a1
import Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph__p2m_f0f39874_5ae5_48cf_ae7d_0d6801141c64_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  classical
  obtain ⟨K, hsub, hconn, hKplanar⟩ :=
    WilliamsonShmoys.planar_connected_supergraph__p2m_f0f39874_5ae5_48cf_ae7d_0d6801141c64_a1
      H hH
  letI : DecidableRel K.Adj := Classical.decRel _
  have hK :=
    WilliamsonShmoys.connected_planar_edge_bound__p2m_f0f39874_5ae5_48cf_ae7d_0d6801141c64_a1
      K hKplanar hconn hcard
  have hHK : H ≤ K := hsub
  have h_edges : H.edgeFinset.card ≤ K.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hHK)
  omega
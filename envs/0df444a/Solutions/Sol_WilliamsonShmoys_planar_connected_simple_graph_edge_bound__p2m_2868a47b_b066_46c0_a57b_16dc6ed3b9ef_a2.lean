-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_simple_graph_edge_bound__p2m_2868a47b_b066_46c0_a57b_16dc6ed3b9ef_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:38:59.970598+00:00
-- url     : https://prove2.me/submissions/34c6cd49-e190-42ea-9c53-68453aec32dc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension__p2m_5e0b2c41_06cd_4cea_b53d_448657bee65e_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : G.Connected) :
    G.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, dH, _hH, hsub, hHcard⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_extension__p2m_5e0b2c41_06cd_4cea_b53d_448657bee65e_a1
      G hG hcard hconn
  letI : DecidableRel H.Adj := dH
  have hEdges : G.edgeFinset ⊆ H.edgeFinset :=
    SimpleGraph.edgeFinset_mono hsub
  have hle : G.edgeFinset.card ≤ H.edgeFinset.card := Finset.card_le_card hEdges
  omega
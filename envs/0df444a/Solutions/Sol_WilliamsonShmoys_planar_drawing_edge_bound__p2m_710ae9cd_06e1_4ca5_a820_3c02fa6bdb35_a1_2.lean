-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_710ae9cd_06e1_4ca5_a820_3c02fa6bdb35_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:03:28.657013+00:00
-- url     : https://prove2.me/submissions/7dfce92c-abf8-43a6-b7a0-eae10a52b1e1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_b9db41c8_79f8_4b68_86df_fe1252530a28_a1
import Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph_of_three_vertices__p2m_b9db41c8_79f8_4b68_86df_fe1252530a28_a3
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  classical
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  obtain ⟨K, hHK, hKconn, hKplanar⟩ :=
    WilliamsonShmoys.planar_connected_supergraph_of_three_vertices__p2m_b9db41c8_79f8_4b68_86df_fe1252530a28_a3
      H hH hcard
  have hKbound :=
    WilliamsonShmoys.connected_planar_edge_bound__p2m_b9db41c8_79f8_4b68_86df_fe1252530a28_a1
      K hKconn hKplanar hcard
  calc
    H.edgeFinset.card ≤ K.edgeFinset.card :=
      Finset.card_le_card (SimpleGraph.edgeFinset_mono hHK)
    _ ≤ 3 * Fintype.card V - 6 := hKbound
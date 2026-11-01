-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_graph_edge_count_upper__p2m_ad02c9e2_6f74_49a1_ae0d_05fd18f8b6b9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:18:02.071247+00:00
-- url     : https://prove2.me/submissions/8f2728c5-6919-4c76-bae3-105ca37016b1

import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_b89122c2_2828_407e_ad92_2701689cab61_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hcard : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_bound__p2m_b89122c2_2828_407e_ad92_2701689cab61_a1 H hH hcard

-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_2d00307b_e04d_4990_9e5d_cdabacc381df_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:25:17.950993+00:00
-- url     : https://prove2.me/submissions/81fe08d5-3eaa-4914-a926-917b69d3de5c

import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_maximal_edge_count_20261026

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.planar_supergraph_triangulation_maximal_edge_count_20261026 H hplanar hV hmax

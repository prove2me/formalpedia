-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_8532617a_0690_495a_a2cc_fdaf4080cf05_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:16:38.351945+00:00
-- url     : https://prove2.me/submissions/62092c48-d6d2-4a7f-b7b5-6fe22f5f8950

import Theorems.Thm_WilliamsonShmoys_exists_drawable_edge_count_upper_bound
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.exists_drawable_edge_count_upper_bound G hcard hG

-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_exact_edges_4f89c2_planar_edge_count_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:46:45.992985+00:00
-- url     : https://prove2.me/submissions/523a9eb0-d4c6-4304-9027-b458a586bedb

import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_edgeSet_ncard_le

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    R.edgeSet.ncard <= 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planarDrawingOn_edgeSet_ncard_le R hV hR

-- Prove2me | solution 2 for WilliamsonShmoys.planar_triangulated_supergraph__p2m_7a004575_a295_4f3c_8d74_3fb00efa8d41_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:11:39.049721+00:00
-- url     : https://prove2.me/submissions/6100d128-9671-4a62-89c5-c06e8f80871e

import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_maximal_edge_count__p2m_d65752b0_c280_4c98_926b_0ae69c395723_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.planar_supergraph_with_maximal_edge_count__p2m_d65752b0_c280_4c98_926b_0ae69c395723_a1 H hH hV

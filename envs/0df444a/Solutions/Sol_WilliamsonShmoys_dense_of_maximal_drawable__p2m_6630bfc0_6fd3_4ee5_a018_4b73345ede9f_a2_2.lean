-- Prove2me | solution 2 for WilliamsonShmoys.dense_of_maximal_drawable__p2m_6630bfc0_6fd3_4ee5_a018_4b73345ede9f_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:17:48.336069+00:00
-- url     : https://prove2.me/submissions/c6e44c59-1d22-40d3-80c2-34ef2080f22d

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_v2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (hDraw : HasPlanarDrawingOn Q) (hMax : ∀ R : SimpleGraph V, Q ≤ R → HasPlanarDrawingOn R → R ≤ Q) (hV : 3 ≤ Fintype.card V) : 3 * Fintype.card V ≤ Q.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_planar_edge_lower_bound_v2 Q hDraw hMax hV

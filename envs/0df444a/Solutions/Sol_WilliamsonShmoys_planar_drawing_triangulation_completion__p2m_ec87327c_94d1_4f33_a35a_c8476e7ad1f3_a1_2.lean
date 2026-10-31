-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_ec87327c_94d1_4f33_a35a_c8476e7ad1f3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:03:23.866344+00:00
-- url     : https://prove2.me/submissions/1fc2fc1f-209c-44c2-9285-f2cb0d687e03

import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_maximal_edge_count__p2m_d65752b0_c280_4c98_926b_0ae69c395723_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H) (hCard : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧ K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.planar_supergraph_with_maximal_edge_count__p2m_d65752b0_c280_4c98_926b_0ae69c395723_a1 H hDraw hCard

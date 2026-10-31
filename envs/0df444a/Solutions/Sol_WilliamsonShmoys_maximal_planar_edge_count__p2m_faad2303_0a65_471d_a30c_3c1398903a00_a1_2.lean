-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_faad2303_0a65_471d_a30c_3c1398903a00_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:37:22.231617+00:00
-- url     : https://prove2.me/submissions/c9ac808b-beff-4be0-83ea-5eceb8b33704

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound_triangulation_completion_maximal_planar_edge_count

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) : H.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound_triangulation_completion_maximal_planar_edge_count H hH hV hMax

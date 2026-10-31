-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_43831d01_c2a2_47cc_baf7_12299ab7bdf8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:01:33.980996+00:00
-- url     : https://prove2.me/submissions/895f4fda-c8e3-4cac-8722-f44e7eeb0952

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound_for_triangulation_1e14dc85_fe67_4e30_934e_c619828dd605

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hV : 3 <= Fintype.card V) (hmax : ∀ J : SimpleGraph V, H <= J → HasPlanarDrawingOn J → J <= H) : 3 * Fintype.card V = H.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_planar_drawing_edge_bound_for_triangulation_1e14dc85_fe67_4e30_934e_c619828dd605 H hH hV hmax

-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawable_edge_count_upper__p2m_8e3b1f8a_4617_463b_ae07_33ab92d25c24_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:32:41.596359+00:00
-- url     : https://prove2.me/submissions/4604919c-42d6-4e1b-9998-463b64ff0db6

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G) (hCard : 3 <= Fintype.card V) : G.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound G hDraw hCard

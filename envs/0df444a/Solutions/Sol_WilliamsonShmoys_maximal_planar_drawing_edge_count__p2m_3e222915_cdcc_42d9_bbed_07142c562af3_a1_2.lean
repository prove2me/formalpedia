-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_3e222915_cdcc_42d9_bbed_07142c562af3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:33:57.685847+00:00
-- url     : https://prove2.me/submissions/d271d05e-7e4c-489c-aae7-2571776df71c

import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_maximal_edge_count_20261026

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (X : SimpleGraph V) (hX : WilliamsonShmoys.HasPlanarDrawingOn X) (hV : 3 ≤ Fintype.card V) (hmax : ∀ Y : SimpleGraph V, X ≤ Y → WilliamsonShmoys.HasPlanarDrawingOn Y → Y = X) : X.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.planar_supergraph_triangulation_maximal_edge_count_20261026 X hX hV hmax

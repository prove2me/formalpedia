-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_444bbc12_374a_443e_a15d_6bd6256fef03_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:32:47.491988+00:00
-- url     : https://prove2.me/submissions/3ca74ee4-6a29-4e4b-bd76-cce890f170ed

import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_maximal_edge_count_20261026

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (Y : SimpleGraph V) (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) (hV : 3 ≤ Fintype.card V) (hYmax : ∀ Z : SimpleGraph V, Y ≤ Z → WilliamsonShmoys.HasPlanarDrawingOn Z → Z = Y) : Y.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.planar_supergraph_triangulation_maximal_edge_count_20261026 Y hY hV hYmax

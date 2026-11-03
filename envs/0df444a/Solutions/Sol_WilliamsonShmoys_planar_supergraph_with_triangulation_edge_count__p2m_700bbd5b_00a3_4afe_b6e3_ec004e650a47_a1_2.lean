-- Prove2me | solution 2 for WilliamsonShmoys.planar_supergraph_with_triangulation_edge_count__p2m_700bbd5b_00a3_4afe_b6e3_ec004e650a47_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:58:27.467647+00:00
-- url     : https://prove2.me/submissions/5fa76e2b-bc0c-4dec-8a98-72ad1e6aea97

import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_9948da09_8892_4f55_9a10_a3a5f578a96b_a1
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V, G ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_triangulation_extension__p2m_9948da09_8892_4f55_9a10_a3a5f578a96b_a1 G hG hcard
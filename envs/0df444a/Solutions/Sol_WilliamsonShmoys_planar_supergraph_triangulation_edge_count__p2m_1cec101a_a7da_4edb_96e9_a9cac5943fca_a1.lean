-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_triangulation_edge_count__p2m_1cec101a_a7da_4edb_96e9_a9cac5943fca_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:08:31.620523+00:00
-- url     : https://prove2.me/submissions/183d8e6b-a2d0-4317-a88a-f469c2d3bfd6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_supergraph__p2m_db367b77_db98_427b_b1c6_513aa1e72eeb_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_db367b77_db98_427b_b1c6_513aa1e72eeb_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hDraw : HasPlanarDrawingOn N)
    (hV : 3 <= Fintype.card V) :
    exists P : SimpleGraph V, N <= P /\ HasPlanarDrawingOn P /\
      P.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨P, hNP, hPDraw, hMax⟩ :=
    WilliamsonShmoys.planar_edge_maximal_supergraph__p2m_db367b77_db98_427b_b1c6_513aa1e72eeb_a1
      N hDraw
  exact ⟨P, hNP, hPDraw,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_db367b77_db98_427b_b1c6_513aa1e72eeb_a1
      P hPDraw hV hMax⟩
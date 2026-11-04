-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_23fbcf6b_b479_4c5b_ac5b_aebde1c2012f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:35:49.141749+00:00
-- url     : https://prove2.me/submissions/b2daa6aa-daa7-4518-8b80-a3ce51c74b65

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (hN : HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V) :
    N.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  classical
  have h := WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound N hN hcard
  simpa only [← N.coe_edgeFinset, Set.ncard_coe_finset] using h

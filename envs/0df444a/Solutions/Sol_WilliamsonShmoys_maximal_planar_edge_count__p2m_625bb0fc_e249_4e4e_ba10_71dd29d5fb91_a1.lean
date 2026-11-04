-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_625bb0fc_e249_4e4e_ba10_71dd29d5fb91_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:28:55.07696+00:00
-- url     : https://prove2.me/submissions/dbba0b12-e967-47d1-a7cf-fcc7a27a793d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_23fbcf6b_b479_4c5b_ac5b_aebde1c2012f_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_23fbcf6b_b479_4c5b_ac5b_aebde1c2012f_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (hN : HasPlanarDrawingOn N)
    (hmax : forall K : SimpleGraph V, N <= K -> HasPlanarDrawingOn K -> K = N)
    (hcard : 3 <= Fintype.card V) :
    6 * Fintype.card V = 2 * N.edgeFinset.card + 12 := by
  have hup := WilliamsonShmoys.planar_drawing_edge_bound__p2m_23fbcf6b_b479_4c5b_ac5b_aebde1c2012f_a1
    N dN hN hcard
  have hlo := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_23fbcf6b_b479_4c5b_ac5b_aebde1c2012f_a1
    N dN hN hmax hcard
  omega
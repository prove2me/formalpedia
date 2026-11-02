-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_94636b31_2f9e_4256_93d0_7a9950cdcd71_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:37:02.050632+00:00
-- url     : https://prove2.me/submissions/be434a4d-37d2-4c02-8be1-9af404ba8ad5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_upper__p2m_43ff6658_223d_4a7a_89b3_fa5ada87c7e3_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower__p2m_43ff6658_223d_4a7a_89b3_fa5ada87c7e3_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ (K : SimpleGraph V) [DecidableRel K.Adj],
      HasPlanarDrawingOn K → H ≤ K → K ≤ H) :
    H.edgeFinset.card + 6 = 3 * Fintype.card V := by
  have hu := WilliamsonShmoys.planar_simple_edge_upper__p2m_43ff6658_223d_4a7a_89b3_fa5ada87c7e3_a1
    H hH hcard
  have hl := WilliamsonShmoys.maximal_planar_edge_lower__p2m_43ff6658_223d_4a7a_89b3_fa5ada87c7e3_a1
    H hH hcard hmax
  omega
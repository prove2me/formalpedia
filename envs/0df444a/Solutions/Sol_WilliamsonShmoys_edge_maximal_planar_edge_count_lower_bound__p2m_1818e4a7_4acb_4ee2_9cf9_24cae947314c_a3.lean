-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_edge_count_lower_bound__p2m_1818e4a7_4acb_4ee2_9cf9_24cae947314c_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:00:03.025257+00:00
-- url     : https://prove2.me/submissions/b387ad2b-8f0b-4938-b8d1-661b5fc0ea28
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count_euler_incidence__p2m_2b14c079_901b_4d89_85a0_5d7005f21dc0_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U)
    (hmax : ∀ (W : SimpleGraph V) (dW : DecidableRel W.Adj),
      HasPlanarDrawingOn W →
      (letI : DecidableRel U.Adj := dU
       letI : DecidableRel W.Adj := dW
       U.edgeFinset ⊆ W.edgeFinset) →
      (letI : DecidableRel U.Adj := dU
       letI : DecidableRel W.Adj := dW
       W.edgeFinset ⊆ U.edgeFinset))
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel U.Adj := dU
     3 * Fintype.card V - 6 ≤ U.edgeFinset.card) := by
  letI : DecidableRel U.Adj := dU
  obtain ⟨f, heuler, hinc⟩ :=
    WilliamsonShmoys.maximal_planar_face_count_euler_incidence__p2m_2b14c079_901b_4d89_85a0_5d7005f21dc0_a1
      U dU hU hmax hcard
  omega
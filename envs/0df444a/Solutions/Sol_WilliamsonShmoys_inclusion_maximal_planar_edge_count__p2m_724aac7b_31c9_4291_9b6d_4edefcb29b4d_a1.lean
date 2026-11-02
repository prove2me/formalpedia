-- Prove2me | solution 1 for WilliamsonShmoys.inclusion_maximal_planar_edge_count__p2m_724aac7b_31c9_4291_9b6d_4edefcb29b4d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:09:43.37749+00:00
-- url     : https://prove2.me/submissions/c22760f4-0769-487a-9c56-37ef4b2b366b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count__p2m_15adcf76_f3b0_4eb0_a8d6_6562dc150ecb_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ (K : SimpleGraph V) [DecidableRel K.Adj],
      HasPlanarDrawingOn K → H ≤ K → K ≤ H) :
    H.edgeFinset.card + 6 = 3 * Fintype.card V := by
  obtain ⟨f, heuler, hfaces⟩ :=
    WilliamsonShmoys.maximal_planar_face_count__p2m_15adcf76_f3b0_4eb0_a8d6_6562dc150ecb_a1
      H hH hcard hmax
  omega
-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_0f5981a3_7974_4822_a476_e1c2ba671214_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:33:52.482866+00:00
-- url     : https://prove2.me/submissions/e8363d58-2be1-4782-b433-4e520c5888fa

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_six_offset_lower_bound
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hP : HasPlanarDrawingOn P)
    (hmax : ∀ Q : SimpleGraph V,
      (∀ u v, P.Adj u v → Q.Adj u v) →
      HasPlanarDrawingOn Q →
      (∀ u v, Q.Adj u v → P.Adj u v)) :
    3 * Fintype.card V ≤ P.edgeSet.ncard + 6 := by
  apply WilliamsonShmoys.maximal_planar_drawing_six_offset_lower_bound P hP
  · intro Q hQ hsub
    exact hmax Q hsub hQ
  · exact hcard

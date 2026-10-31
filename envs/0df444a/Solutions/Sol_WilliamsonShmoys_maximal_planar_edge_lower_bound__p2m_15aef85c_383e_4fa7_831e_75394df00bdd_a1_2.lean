-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_15aef85c_383e_4fa7_831e_75394df00bdd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:58:15.862429+00:00
-- url     : https://prove2.me/submissions/682c455a-6c8e-4ba3-bf09-c96437665fc6

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound_9f95e338

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_9f95e338 H hH hV hmax

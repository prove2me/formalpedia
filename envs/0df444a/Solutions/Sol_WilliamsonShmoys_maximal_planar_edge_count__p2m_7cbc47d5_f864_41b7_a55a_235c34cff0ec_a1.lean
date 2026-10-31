-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_7cbc47d5_f864_41b7_a55a_235c34cff0ec_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:09:13.498903+00:00
-- url     : https://prove2.me/submissions/5edb74d9-a64d-44d1-8333-53f2aad0494a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_15aef85c_383e_4fa7_831e_75394df00bdd_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_15aef85c_383e_4fa7_831e_75394df00bdd_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.planar_edge_upper_bound__p2m_15aef85c_383e_4fa7_831e_75394df00bdd_a1 H hH hV
  have hlower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_15aef85c_383e_4fa7_831e_75394df00bdd_a1 H hH hV hmax
  omega
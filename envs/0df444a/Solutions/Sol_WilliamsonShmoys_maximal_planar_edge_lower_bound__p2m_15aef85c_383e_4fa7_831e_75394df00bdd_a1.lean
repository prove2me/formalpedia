-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_15aef85c_383e_4fa7_831e_75394df00bdd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:22:06.000872+00:00
-- url     : https://prove2.me/submissions/cb1a0ad3-b470-4550-b55a-77dcb884d651

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_b4d3c156_327f_4a72_8089_248d3313a19e_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hK, hcard⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_b4d3c156_327f_4a72_8089_248d3313a19e_a1
      H hH hV
  have hKH : K ≤ H := hmax K hHK hK
  have hEq : H = K := le_antisymm hHK hKH
  have hcardH : H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
    simpa [hEq] using hcard
  nlinarith
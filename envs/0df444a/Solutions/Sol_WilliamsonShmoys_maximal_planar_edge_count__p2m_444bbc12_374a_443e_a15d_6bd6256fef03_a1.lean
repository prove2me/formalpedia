-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_444bbc12_374a_443e_a15d_6bd6256fef03_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:29:53.386633+00:00
-- url     : https://prove2.me/submissions/63cbff67-c85d-4588-a7b8-ac54eb9a850f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_bd652ef6_f935_4766_81fb_919843a61889_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_bd652ef6_f935_4766_81fb_919843a61889_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hV : 3 ≤ Fintype.card V)
    (hYmax : ∀ Z : SimpleGraph V, Y ≤ Z → WilliamsonShmoys.HasPlanarDrawingOn Z → Z = Y) :
    Y.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper :=
    WilliamsonShmoys.planar_edge_count_upper_bound__p2m_bd652ef6_f935_4766_81fb_919843a61889_a1
      Y hY hV
  have hlower :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_bd652ef6_f935_4766_81fb_919843a61889_a1
      Y hY hV hYmax
  omega
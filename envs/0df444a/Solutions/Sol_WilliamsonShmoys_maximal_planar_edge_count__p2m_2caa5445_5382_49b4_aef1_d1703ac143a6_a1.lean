-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_2caa5445_5382_49b4_aef1_d1703ac143a6_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:24:19.951506+00:00
-- url     : https://prove2.me/submissions/df10a43e-4fd3-4c9c-9e30-1956f033b733
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_d8c6ec37_9497_4022_a1c3_e053f306de5e_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_d8c6ec37_9497_4022_a1c3_e053f306de5e_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hup : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.planar_edge_count_upper_bound__p2m_d8c6ec37_9497_4022_a1c3_e053f306de5e_a1
      H hH hCard
  have hlo : 3 * Fintype.card V ≤ H.edgeSet.ncard + 6 :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_d8c6ec37_9497_4022_a1c3_e053f306de5e_a1
      H hH hCard hmax
  omega
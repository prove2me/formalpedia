-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_exact_edge_count__p2m_55782cbf_98ab_4cab_bb1c_268796d1154e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T06:43:07.500986+00:00
-- url     : https://prove2.me/submissions/0fd7faa2-7c9d-49e4-a889-b44ecb36fc97

import Mathlib.Tactic
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_fa30b313_3ade_47b7_9dcc_bae00c9eb7a0_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_fa30b313_3ade_47b7_9dcc_bae00c9eb7a0_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hMplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : forall N : SimpleGraph V,
      M.edgeSet <= N.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn N ->
      N.edgeSet = M.edgeSet) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.planar_drawing_edge_bound__p2m_fa30b313_3ade_47b7_9dcc_bae00c9eb7a0_a1
    M hV hMplanar
  have hlower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_fa30b313_3ade_47b7_9dcc_bae00c9eb7a0_a1
    M hV hMplanar hmax
  omega
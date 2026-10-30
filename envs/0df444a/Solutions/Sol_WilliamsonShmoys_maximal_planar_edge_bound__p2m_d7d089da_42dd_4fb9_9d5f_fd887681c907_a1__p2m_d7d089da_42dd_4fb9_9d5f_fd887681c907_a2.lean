-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound__p2m_d7d089da_42dd_4fb9_9d5f_fd887681c907_a1__p2m_d7d089da_42dd_4fb9_9d5f_fd887681c907_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T06:27:31.949036+00:00
-- url     : https://prove2.me/submissions/694d41ee-db4c-4d40-9b2a-41211291fabf

import Mathlib.Tactic
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_exact_edge_count__p2m_55782cbf_98ab_4cab_bb1c_268796d1154e_a2
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
    3 * Fintype.card V <= M.edgeSet.ncard + 6 := by
  have hExact := WilliamsonShmoys.maximal_planar_exact_edge_count__p2m_55782cbf_98ab_4cab_bb1c_268796d1154e_a2
    M hV hMplanar hmax
  omega
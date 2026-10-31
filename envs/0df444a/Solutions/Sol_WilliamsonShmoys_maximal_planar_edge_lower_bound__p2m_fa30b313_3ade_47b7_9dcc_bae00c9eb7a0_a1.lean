-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_fa30b313_3ade_47b7_9dcc_bae00c9eb7a0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:33:50.281062+00:00
-- url     : https://prove2.me/submissions/ac60938c-11b1-401a-aaf6-e5164a5df4d8

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_d7d089da_42dd_4fb9_9d5f_fd887681c907_a1__p2m_d7d089da_42dd_4fb9_9d5f_fd887681c907_a2

import Mathlib.Tactic
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
    3 * Fintype.card V <= M.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_planar_edge_bound__p2m_d7d089da_42dd_4fb9_9d5f_fd887681c907_a1__p2m_d7d089da_42dd_4fb9_9d5f_fd887681c907_a2 M hV hMplanar hmax

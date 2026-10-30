-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound__p2m_fa1358d7_5b01_463f_a67b_1e1bbf77dca7_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:33:08.978101+00:00
-- url     : https://prove2.me/submissions/e80b384a-c99c-484c-873d-46a5dfe86fbf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_connected_induced__p2m_66ade5d4_3842_4532_bbd5_36e43a15d1f5_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_connected_induced__p2m_66ade5d4_3842_4532_bbd5_36e43a15d1f5_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  apply WilliamsonShmoys.planar_edge_bound_from_connected_induced__p2m_66ade5d4_3842_4532_bbd5_36e43a15d1f5_a1 H hCard
  intro s hconn hs
  exact WilliamsonShmoys.planar_edge_bound_connected_induced__p2m_66ade5d4_3842_4532_bbd5_36e43a15d1f5_a1 H hH s hconn hs
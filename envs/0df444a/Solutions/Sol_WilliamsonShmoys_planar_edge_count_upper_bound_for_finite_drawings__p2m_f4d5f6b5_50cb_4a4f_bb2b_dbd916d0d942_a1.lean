-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_for_finite_drawings__p2m_f4d5f6b5_50cb_4a4f_bb2b_dbd916d0d942_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T08:22:37.286237+00:00
-- url     : https://prove2.me/submissions/e0c7ddf8-e659-437d-b576-57c6d7106b6b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_b1eeea0d_0264_4037_a9be_26c96369c701_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V) :
    M.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  classical
  letI : DecidableRel M.Adj := dM
  calc
    M.edgeFinset.card = Fintype.card M.edgeSet := SimpleGraph.edgeFinset_card
    _ = M.edgeSet.ncard := Set.fintypeCard_eq_ncard M.edgeSet
    _ <= 3 * Fintype.card V - 6 :=
      WilliamsonShmoys.planar_edge_count_upper_bound__p2m_b1eeea0d_0264_4037_a9be_26c96369c701_a1
        M hcard hM

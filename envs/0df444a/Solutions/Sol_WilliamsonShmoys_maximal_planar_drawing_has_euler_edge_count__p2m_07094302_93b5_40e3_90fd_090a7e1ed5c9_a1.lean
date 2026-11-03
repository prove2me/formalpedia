-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_euler_edge_count__p2m_07094302_93b5_40e3_90fd_090a7e1ed5c9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T11:58:32.96521+00:00
-- url     : https://prove2.me/submissions/c39a27c1-f45a-4678-a09f-88b33a2bed9c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_euler_7e0405ab
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hn : 3 ≤ Fintype.card V)
    (hmax : ∀ (J : SimpleGraph V), H ≤ J →
      WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H) :
    (letI : DecidableRel H.Adj := dH;
      H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  letI : DecidableRel H.Adj := dH
  have h := WilliamsonShmoys.maximal_planar_edge_count_euler_7e0405ab H hH hn hmax
  have hc : H.edgeFinset.card + 6 = 3 * Fintype.card V := by
    simpa only [← SimpleGraph.coe_edgeFinset H, Set.ncard_coe_finset] using h
  omega

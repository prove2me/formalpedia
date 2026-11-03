-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler__p2m_817efdd6_f4a1_4a63_bdc1_5f87cd74d1d4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T11:55:32.859636+00:00
-- url     : https://prove2.me/submissions/7e2e3899-5a8f-4a82-9109-3b20ef28c6d3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_formula

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    [DecidableRel M.Adj] (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hconn : M.Connected) :
    ∃ f : ℕ, Fintype.card V + f = M.edgeFinset.card + 2 := by
  simpa only [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard] using
    (WilliamsonShmoys.connected_planar_drawing_euler_formula M hconn hM)

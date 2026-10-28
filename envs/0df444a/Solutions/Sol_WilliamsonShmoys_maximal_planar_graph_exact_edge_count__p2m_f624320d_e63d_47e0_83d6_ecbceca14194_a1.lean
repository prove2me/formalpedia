-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_f624320d_e63d_47e0_83d6_ecbceca14194_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:10:20.272204+00:00
-- url     : https://prove2.me/submissions/54bdac23-2c3a-4877-9446-576bd202ee55
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_completion_exact_edge_count__p2m_c3a9b232_8896_4daf_b121_720ec89c3bee_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hMaximal : forall K : SimpleGraph V,
      N <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K <= N)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hNH, hH, hCount⟩ :=
    WilliamsonShmoys.planar_supergraph_completion_exact_edge_count__p2m_c3a9b232_8896_4daf_b121_720ec89c3bee_a1 N hV hN
  have hHN : H <= N := hMaximal H hNH hH
  have hEq : H = N := le_antisymm hHN hNH
  simpa [hEq] using hCount
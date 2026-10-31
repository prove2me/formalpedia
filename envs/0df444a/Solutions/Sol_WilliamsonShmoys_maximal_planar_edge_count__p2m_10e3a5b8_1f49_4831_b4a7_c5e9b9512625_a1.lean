-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_10e3a5b8_1f49_4831_b4a7_c5e9b9512625_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:24:52.38043+00:00
-- url     : https://prove2.me/submissions/cba0ea60-1d28-44f7-951b-e4f8f1e68b65

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_exact_edge_count_extension__p2m_05b862e6_965f_4ca7_859a_791049e91053_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M)
    (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hDrawN, hCount⟩ :=
    WilliamsonShmoys.planar_graph_has_exact_edge_count_extension__p2m_05b862e6_965f_4ca7_859a_791049e91053_a1
      M hDraw hV
  have hNM : N ≤ M := hMax N hMN hDrawN
  have hEq : M = N := le_antisymm hMN hNM
  simpa [hEq] using hCount
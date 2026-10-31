-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_50304f69_3f87_43f6_91bb_4f1f44440925_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:39:37.798656+00:00
-- url     : https://prove2.me/submissions/e135f4ab-7fc4-4ef1-b7d7-5426fbd156a2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_exact_edge_count_supergraph__p2m_76d78def_4fcc_4b45_b88b_61d6f8602e64_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (S : SimpleGraph V) (hDraw : HasPlanarDrawingOn S) (hV : 3 <= Fintype.card V) (hMax : forall T : SimpleGraph V, S <= T -> HasPlanarDrawingOn T -> T = S) : 3 * Fintype.card V - 6 <= S.edgeSet.ncard := by
  obtain ⟨T, hST, hTDraw, hCount⟩ := WilliamsonShmoys.planar_graph_has_exact_edge_count_supergraph__p2m_76d78def_4fcc_4b45_b88b_61d6f8602e64_a1 S hDraw hV
  have hEq : T = S := hMax T hST hTDraw
  rw [hEq] at hCount
  exact le_of_eq hCount
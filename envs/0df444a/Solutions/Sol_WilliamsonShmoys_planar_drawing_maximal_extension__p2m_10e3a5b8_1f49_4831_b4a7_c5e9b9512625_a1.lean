-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_10e3a5b8_1f49_4831_b4a7_c5e9b9512625_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:26:29.399973+00:00
-- url     : https://prove2.me/submissions/bdcb3a11-7c11-49cb-aa8c-898e64a505ce

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_exists_maximal_simpleGraph_supergraph_of_finite__p2m_4cee4fb6_81c0_44bc_ba4b_b191f8c55242_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M := by
  obtain ⟨M, hLM, hM, hMax⟩ :=
    exists_maximal_simpleGraph_supergraph_of_finite__p2m_4cee4fb6_81c0_44bc_ba4b_b191f8c55242_a1
      (L := L) (P := HasPlanarDrawingOn) hDraw
  exact ⟨M, hLM, hM, hMax⟩
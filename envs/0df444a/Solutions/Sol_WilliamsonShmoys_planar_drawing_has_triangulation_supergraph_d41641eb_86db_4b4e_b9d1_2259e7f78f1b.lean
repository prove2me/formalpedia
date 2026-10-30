-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulation_supergraph_d41641eb_86db_4b4e_b9d1_2259e7f78f1b
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:12:15.328166+00:00
-- url     : https://prove2.me/submissions/ba7beeed-fc45-4ba7-838a-066b48c465fe

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_supergraph_298b1a86_18b6_4bc5_96f4_b68905059bb9
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count_298b1a86_18b6_4bc5_96f4_b68905059bb9

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hDrawing : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      3 * Fintype.card V = N.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hNdraw, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_drawing_supergraph_298b1a86_18b6_4bc5_96f4_b68905059bb9 M hDrawing
  have hCount := WilliamsonShmoys.maximal_planar_drawing_exact_edge_count_298b1a86_18b6_4bc5_96f4_b68905059bb9
    N hNdraw hCard hMax
  exact ⟨N, hMN, hNdraw, hCount⟩
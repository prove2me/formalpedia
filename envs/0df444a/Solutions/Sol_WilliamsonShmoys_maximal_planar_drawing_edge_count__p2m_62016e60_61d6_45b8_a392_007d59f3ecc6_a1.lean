-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_62016e60_61d6_45b8_a392_007d59f3ecc6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:26:35.936193+00:00
-- url     : https://prove2.me/submissions/39438c7f-196a-41d4-9cfe-5f5033e130ef

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_1129f324_ed56_4814_b878_03ab3968bf96_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hKN, hN, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_1129f324_ed56_4814_b878_03ab3968bf96_a1
      K hV hK
  have hNK : N = K := hmax N hKN hN
  rw [hNK] at hcount
  exact hcount
-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_has_triangulation_edge_count__p2m_a5443f4e_9d41_4300_b6d5_4cb884e21163_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:38:54.334511+00:00
-- url     : https://prove2.me/submissions/05b45d9d-73a5-4a5a-9a94-c8e25edaa723

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulating_supergraph__p2m_af48b21b_c55d_4bf2_b112_9c52085bd66b_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hDrawL, hCount⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulating_supergraph__p2m_af48b21b_c55d_4bf2_b112_9c52085bd66b_a1
      K hDraw hV
  have hEq : L = K := hMax L hKL hDrawL
  rw [← hEq]
  exact hCount
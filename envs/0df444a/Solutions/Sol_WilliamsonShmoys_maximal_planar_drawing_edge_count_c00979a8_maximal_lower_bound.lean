-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_c00979a8_maximal_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:26:41.700753+00:00
-- url     : https://prove2.me/submissions/158256db-be68-40f6-b9cc-d6427cc1c505

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_completion_c00979a8

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K <= L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hbound⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_completion_c00979a8 K hV hK
  have hEq : L = K := hmax L hKL hL
  rw [hEq] at hbound
  exact hbound
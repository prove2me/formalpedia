-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_630b5c25_00a7_4258_a685_bfcae7eacbce_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:04:17.758509+00:00
-- url     : https://prove2.me/submissions/cd00234e-7cc3-457e-a9be-3637d4979407

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_edge_bound__p2m_a676df72_8370_487d_8148_6fb0674d69c1_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 <= Fintype.card V)
    (hmax : forall N : SimpleGraph V, M <= N -> HasPlanarDrawingOn N -> N = M) :
    3 * Fintype.card V <= M.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hN, hbound⟩ :=
    WilliamsonShmoys.planar_completion_edge_bound__p2m_a676df72_8370_487d_8148_6fb0674d69c1_a2
      M hM hV
  have hNM : N = M := hmax N hMN hN
  rw [← hNM]
  exact hbound
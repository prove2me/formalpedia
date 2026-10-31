-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_ebb4e414_4dfa_4f3a_826b_c9f7b30cda57_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:06:04.853512+00:00
-- url     : https://prove2.me/submissions/f9233f11-f266-4fb4-9235-b321a97fdac6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_edge_count__p2m_799e183d_d2a5_4361_a072_2ee077486503_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ J : SimpleGraph V,
      H ≤ J →
      WilliamsonShmoys.HasPlanarDrawingOn J →
      J = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨J, hHJ, hDrawJ, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_edge_count__p2m_799e183d_d2a5_4361_a072_2ee077486503_a1
      H hDraw hV
  have hJH : J = H := hMax J hHJ hDrawJ
  rw [hJH] at hCount
  exact hCount
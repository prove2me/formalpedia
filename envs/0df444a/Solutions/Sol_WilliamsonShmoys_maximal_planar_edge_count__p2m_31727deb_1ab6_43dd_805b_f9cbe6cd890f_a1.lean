-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_31727deb_1ab6_43dd_805b_f9cbe6cd890f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:57:31.729795+00:00
-- url     : https://prove2.me/submissions/46e61d2c-2fbc-4af0-ae97-ace771670dfe

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion__p2m_c53df50c_1a0d_40bf_9101_a79054d6b09a_a1
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (Z : SimpleGraph V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ W : SimpleGraph V, Z ≤ W →
      WilliamsonShmoys.HasPlanarDrawingOn W → W ≤ Z) :
    Z.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨W, hZW, hW, hcard⟩ :=
    WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_c53df50c_1a0d_40bf_9101_a79054d6b09a_a1
      Z hZ hV
  have hWZ : W ≤ Z := hmax W hZW hW
  have hEq : W = Z := le_antisymm hWZ hZW
  simpa [hEq] using hcard
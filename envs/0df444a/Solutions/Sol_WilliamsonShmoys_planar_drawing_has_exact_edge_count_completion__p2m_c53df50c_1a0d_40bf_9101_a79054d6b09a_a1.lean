-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_c53df50c_1a0d_40bf_9101_a79054d6b09a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:12:33.407412+00:00
-- url     : https://prove2.me/submissions/d6775e08-5404-44fd-9df6-3ea0f99fb530

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_909211f8_1bd2_4cd4_92bd_2f3f10d1674e_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_909211f8_1bd2_4cd4_92bd_2f3f10d1674e_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (Z : SimpleGraph V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z)
    (hV : 3 ≤ Fintype.card V) :
    ∃ W : SimpleGraph V, Z ≤ W ∧ WilliamsonShmoys.HasPlanarDrawingOn W ∧
      W.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨W, hZW, hW, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_909211f8_1bd2_4cd4_92bd_2f3f10d1674e_a1
      Z hZ
  exact ⟨W, hZW, hW,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_909211f8_1bd2_4cd4_92bd_2f3f10d1674e_a1
      W hW hmax hV⟩
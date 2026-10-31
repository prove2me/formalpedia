-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_90a6eb8a_5322_4ab0_9f54_46d0ab83dbd2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:00:08.736296+00:00
-- url     : https://prove2.me/submissions/048596a6-f1ca-43e0-a4b2-63aa0e96a0a7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_ccd23c49_4232_4eaf_832f_2977e75f86e1_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_ccd23c49_4232_4eaf_832f_2977e75f86e1_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N ≤ M) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  have hUpper := WilliamsonShmoys.planar_edge_count_upper__p2m_ccd23c49_4232_4eaf_832f_2977e75f86e1_a1
    M hM hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_ccd23c49_4232_4eaf_832f_2977e75f86e1_a1
    M hM hCard hMax
  omega
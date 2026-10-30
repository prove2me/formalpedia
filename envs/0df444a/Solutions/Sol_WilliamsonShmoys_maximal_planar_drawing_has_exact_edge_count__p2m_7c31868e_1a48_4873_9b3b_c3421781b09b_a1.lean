-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_exact_edge_count__p2m_7c31868e_1a48_4873_9b3b_c3421781b09b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:01:55.812946+00:00
-- url     : https://prove2.me/submissions/eb274cb4-653b-4934-93b3-3c283333f59f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_c39276d2_5642_44b6_8869_8a52171f67f2_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_c39276d2_5642_44b6_8869_8a52171f67f2_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c39276d2_5642_44b6_8869_8a52171f67f2_a1 K hDraw hV
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_c39276d2_5642_44b6_8869_8a52171f67f2_a1 K hDraw hMax hV
  omega
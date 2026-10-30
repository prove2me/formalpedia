-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_edge_count__p2m_799e183d_d2a5_4361_a072_2ee077486503_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:22:38.17912+00:00
-- url     : https://prove2.me/submissions/72f97bd2-2c6e-4bef-92cb-51cd493ee195
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_5c3e2d4d_9b9a_4ad6_be37_e52a0ce51388_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_5c3e2d4d_9b9a_4ad6_be37_e52a0ce51388_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ J : SimpleGraph V,
      H ≤ J ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      J.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨J, hHJ, hJDraw, hJMax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_5c3e2d4d_9b9a_4ad6_be37_e52a0ce51388_a1
      H hDraw hV
  refine ⟨J, hHJ, hJDraw, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_5c3e2d4d_9b9a_4ad6_be37_e52a0ce51388_a1
    J hJDraw hV hJMax
-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_237d0a74_b3e5_4601_9e6d_1aac4d25b642_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:35:31.495855+00:00
-- url     : https://prove2.me/submissions/efbce3de-4c4d-4c67-a4d9-8d26e64b1ddd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_le_three_mul_card_sub_six__p2m_c8bd0d06_bddd_4d97_9a5a_50d50f58bad7_a1
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_count__p2m_c8bd0d06_bddd_4d97_9a5a_50d50f58bad7_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ M : SimpleGraph V,
      L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet.ncard ≤ L.edgeSet.ncard) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.planar_edge_count_le_three_mul_card_sub_six__p2m_c8bd0d06_bddd_4d97_9a5a_50d50f58bad7_a1
    L hplanar hV
  obtain ⟨M, hLM, hMplanar, hMcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_c8bd0d06_bddd_4d97_9a5a_50d50f58bad7_a1
      L hplanar hV
  have hle := hmax M hLM hMplanar
  omega

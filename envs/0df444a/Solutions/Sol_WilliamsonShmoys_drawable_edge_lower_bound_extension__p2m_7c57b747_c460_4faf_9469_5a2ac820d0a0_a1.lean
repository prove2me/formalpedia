-- Prove2me | solution 1 for WilliamsonShmoys.drawable_edge_lower_bound_extension__p2m_7c57b747_c460_4faf_9469_5a2ac820d0a0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:40:25.476503+00:00
-- url     : https://prove2.me/submissions/8e0c7b8a-0a06-40b4-9ae4-74082b8256fe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_edge_maximal_extension__p2m_53305c1c_f1f1_46ad_95d2_bc47d8044b33_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_53305c1c_f1f1_46ad_95d2_bc47d8044b33_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      G ≤ L ∧ HasPlanarDrawingOn L ∧
        3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by
  obtain ⟨L, hGL, hL, hmax⟩ :=
    WilliamsonShmoys.drawable_edge_maximal_extension__p2m_53305c1c_f1f1_46ad_95d2_bc47d8044b33_a1
      G hG
  exact ⟨L, hGL, hL,
    WilliamsonShmoys.maximal_drawable_edge_count__p2m_53305c1c_f1f1_46ad_95d2_bc47d8044b33_a1
      L hL hmax hV⟩
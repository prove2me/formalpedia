-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_completion__p2m_a74b4731_eea6_44e0_b9ad_6ea707b8b09a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:05:19.406605+00:00
-- url     : https://prove2.me/submissions/772f249d-c40f-4f1c-a083-9cccf33dd48a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_00e8ebb5_9f6a_4f3b_a13c_8345d9aaf556_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_00e8ebb5_9f6a_4f3b_a13c_8345d9aaf556_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hDraw : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, M.edgeSet ⊆ H.edgeSet ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hSub, hPlanar, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_00e8ebb5_9f6a_4f3b_a13c_8345d9aaf556_a1
      M hDraw
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_00e8ebb5_9f6a_4f3b_a13c_8345d9aaf556_a1
      H hPlanar hCard hMax
  exact ⟨H, hSub, hCount⟩
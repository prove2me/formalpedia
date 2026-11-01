-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_5253a5b4_e9a3_4062_83c0_61b2b3da7c3e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:08:07.401602+00:00
-- url     : https://prove2.me/submissions/2b95e404-4589-4bb5-949b-bc8969d6da51
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_counts__p2m_62c40d5f_afd7_4bfc_ad24_9691a3287af2_a2
import Theorems.Thm_WilliamsonShmoys_planar_face_count_arithmetic__p2m_62c40d5f_afd7_4bfc_ad24_9691a3287af2_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V, H.edgeSet ⊆ J.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn J → J.edgeSet = H.edgeSet)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, heuler, hdegree⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_face_counts__p2m_62c40d5f_afd7_4bfc_ad24_9691a3287af2_a2
      H hplanar hmax hcard
  exact WilliamsonShmoys.planar_face_count_arithmetic__p2m_62c40d5f_afd7_4bfc_ad24_9691a3287af2_a2
    (Fintype.card V) H.edgeSet.ncard f hcard heuler hdegree
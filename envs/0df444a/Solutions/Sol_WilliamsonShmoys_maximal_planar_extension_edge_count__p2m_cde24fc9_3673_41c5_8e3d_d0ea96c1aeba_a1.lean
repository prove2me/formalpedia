-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension_edge_count__p2m_cde24fc9_3673_41c5_8e3d_d0ea96c1aeba_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:37:30.653213+00:00
-- url     : https://prove2.me/submissions/96997eba-31a9-45cc-9fc6-8a1dcd07cf6a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension_exists__p2m_bf2a6b94_c712_4371_81b2_f7600a9fcb4a_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_bf2a6b94_c712_4371_81b2_f7600a9fcb4a_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, H <= K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 = K.edgeSet.ncard := by
  obtain ⟨K, hHK, hK, hMax⟩ :=
    WilliamsonShmoys.maximal_drawable_extension_exists__p2m_bf2a6b94_c712_4371_81b2_f7600a9fcb4a_a1
      H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_bf2a6b94_c712_4371_81b2_f7600a9fcb4a_a1
      K hK hCard hMax⟩
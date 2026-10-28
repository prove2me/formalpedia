-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_completion_d73146df_f66d_4d86_a4dc_57d1ab40d600_v3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:17:50.379229+00:00
-- url     : https://prove2.me/submissions/1815abc4-17e7-4527-bc02-08439379b85e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_54a0e51c_08bc_41d0_9e00_f8ba78b35c82
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_54a0e51c_08bc_41d0_9e00_f8ba78b35c82

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_54a0e51c_08bc_41d0_9e00_f8ba78b35c82 H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_planar_edge_count_54a0e51c_08bc_41d0_9e00_f8ba78b35c82 K hK hV hmax⟩
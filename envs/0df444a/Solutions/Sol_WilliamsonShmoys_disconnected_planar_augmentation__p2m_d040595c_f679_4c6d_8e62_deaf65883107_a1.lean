-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_planar_augmentation__p2m_d040595c_f679_4c6d_8e62_deaf65883107_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:15:46.415645+00:00
-- url     : https://prove2.me/submissions/333c523a-8b30-4af9-b4e0-ef280efee797
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_vertex_partition__p2m_b9f24409_3d4f_491d_a7d1_53a879b4d6a5_a2
import Theorems.Thm_WilliamsonShmoys_join_separated_planar_parts__p2m_b9f24409_3d4f_491d_a7d1_53a879b4d6a5_a2

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hDisc : ¬ M.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ N ≠ M ∧ WilliamsonShmoys.HasPlanarDrawingOn N := by
  obtain ⟨A, hA, hAc, hSep⟩ :=
    WilliamsonShmoys.disconnected_vertex_partition__p2m_b9f24409_3d4f_491d_a7d1_53a879b4d6a5_a2 M hDisc
  exact WilliamsonShmoys.join_separated_planar_parts__p2m_b9f24409_3d4f_491d_a7d1_53a879b4d6a5_a2
    M A hA hAc hSep hM

-- Prove2me | solution 1 for WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_70a8b6e0_c40a_44e8_9147_f9396a2e926b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:37:22.396291+00:00
-- url     : https://prove2.me/submissions/a64e00d9-5c0d-4f66-8a46-5decca7244ef

import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_3e96e4b7_ffaf_421c_b46f_8949f4d2645c_a2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V, G ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M :=
  WilliamsonShmoys.exists_maximal_planar_extension__p2m_3e96e4b7_ffaf_421c_b46f_8949f4d2645c_a2 G hG

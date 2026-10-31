-- Prove2me | solution 1 for WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_45b06a26_f6d7_4266_b401_312835dd7478_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:36:09.546102+00:00
-- url     : https://prove2.me/submissions/4c4d57ed-9824-4534-ada5-d1257dfd8377

import Theorems.Thm_WilliamsonShmoys_same_vertex_maximal_planar_augmentation_extension

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V,
          K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K :=
  WilliamsonShmoys.same_vertex_maximal_planar_augmentation_extension G hG hV

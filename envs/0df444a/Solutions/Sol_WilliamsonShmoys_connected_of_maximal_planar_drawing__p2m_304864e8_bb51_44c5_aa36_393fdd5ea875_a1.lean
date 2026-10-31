-- Prove2me | solution 1 for WilliamsonShmoys.connected_of_maximal_planar_drawing__p2m_304864e8_bb51_44c5_aa36_393fdd5ea875_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:11:31.389056+00:00
-- url     : https://prove2.me/submissions/fada22ce-58a8-4d80-b3d0-88e5efe3219e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_unreachable_vertices__p2m_64b9ded6_6a17_4826_8f9e_3b877457ad0a_a1
import Theorems.Thm_WilliamsonShmoys_augment_planar_drawing_across_components__p2m_64b9ded6_6a17_4826_8f9e_3b877457ad0a_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V) (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hmax : ∀ Z : SimpleGraph V, Y.edgeSet ⊂ Z.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn Z) : Y.Connected := by
  by_contra hconn
  obtain ⟨u, v, huv, hreach⟩ :=
    WilliamsonShmoys.exists_unreachable_vertices__p2m_64b9ded6_6a17_4826_8f9e_3b877457ad0a_a1
      Y hconn
  obtain ⟨Z, hsub, hZ⟩ :=
    WilliamsonShmoys.augment_planar_drawing_across_components__p2m_64b9ded6_6a17_4826_8f9e_3b877457ad0a_a1
      Y hY u v huv hreach
  exact (hmax Z hsub) hZ

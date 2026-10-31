-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_39622fc7_9624_4f8c_802c_be6d654a55c6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:46:41.595996+00:00
-- url     : https://prove2.me/submissions/9490ee1e-f5cf-4d7d-92e0-f8f37c48fba4

import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_3e96e4b7_ffaf_421c_b46f_8949f4d2645c_a2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H :=
  WilliamsonShmoys.exists_maximal_planar_extension__p2m_3e96e4b7_ffaf_421c_b46f_8949f4d2645c_a2 G hG

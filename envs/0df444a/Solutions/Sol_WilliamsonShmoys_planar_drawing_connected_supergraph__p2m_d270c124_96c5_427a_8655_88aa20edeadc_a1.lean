-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_d270c124_96c5_427a_8655_88aa20edeadc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:42:30.300052+00:00
-- url     : https://prove2.me/submissions/c46b3f67-8417-4439-86a0-b3740a536731

import Theorems.Thm_WilliamsonShmoys_exists_connected_planar_supergraph__p2m_c955d1e3_af39_465d_8618_7c677be66dad_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K :=
  WilliamsonShmoys.exists_connected_planar_supergraph__p2m_c955d1e3_af39_465d_8618_7c677be66dad_a1 H hDraw hV

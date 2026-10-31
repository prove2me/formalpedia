-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_extension_exists__p2m_e4b54fa0_8696_482b_974e_2350a87956d8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:02:04.029743+00:00
-- url     : https://prove2.me/submissions/6a652373-a2ad-4388-817b-c8ecf414f373

import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension_cbd57c51e3344f4e814f42afaa7d171b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N) : ∃ Q : SimpleGraph V, N.edgeSet ⊆ Q.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧ ∀ R : SimpleGraph V, Q.edgeSet ⊆ R.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn R → R.edgeSet = Q.edgeSet :=
  WilliamsonShmoys.planar_drawing_has_maximal_extension_cbd57c51e3344f4e814f42afaa7d171b N hDraw

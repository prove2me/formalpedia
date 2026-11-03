-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_has_maximal_planar_supergraph__p2m_80e34e39_9312_4353_9ec3_c3ff17c125fa_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:33:49.640328+00:00
-- url     : https://prove2.me/submissions/adc5581e-5a97-4305-8797-2418e389aaa7

import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_f4d7c237_0776_4adb_8bad_5150d3e32462_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, G.edgeSet ⊆ H.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ (∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn K → K.edgeSet = H.edgeSet) :=
  WilliamsonShmoys.planar_drawing_maximal_extension__p2m_f4d7c237_0776_4adb_8bad_5150d3e32462_a1 G hDraw
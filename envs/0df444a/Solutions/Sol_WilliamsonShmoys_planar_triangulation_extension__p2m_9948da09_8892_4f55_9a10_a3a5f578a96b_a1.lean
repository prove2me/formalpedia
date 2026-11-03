-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_9948da09_8892_4f55_9a10_a3a5f578a96b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T11:55:17.15169+00:00
-- url     : https://prove2.me/submissions/cbc91c08-f988-4ddd-93c3-2e279abc69fd

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_e3ce4704_f609_45f0_9a05_cff1f4f992c7_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      G ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  exact WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_e3ce4704_f609_45f0_9a05_cff1f4f992c7_a1 G hG hcard

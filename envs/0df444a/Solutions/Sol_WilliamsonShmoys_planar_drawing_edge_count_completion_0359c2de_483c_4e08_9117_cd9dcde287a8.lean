-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_completion_0359c2de_483c_4e08_9117_cd9dcde287a8
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:21:16.025157+00:00
-- url     : https://prove2.me/submissions/f8b16678-4ef6-49e2-ae5c-ef525f2c9d64

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension_cbd57c51e3344f4e814f42afaa7d171b
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_cbd57c51e3344f4e814f42afaa7d171b

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      L.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hLH, hH, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_extension_cbd57c51e3344f4e814f42afaa7d171b L hL
  refine ⟨H, hLH, hH, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_edge_count_cbd57c51e3344f4e814f42afaa7d171b H hH hV hMax
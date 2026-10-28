-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:41:28.065706+00:00
-- url     : https://prove2.me/submissions/c47cdf57-bba0-4407-965d-23be5290659e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_exists_maximal_c67fb017
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_maximal_is_connected_c67fb017

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      L ≤ H ∧ H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      L.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨H, hLH, hH, hmax, hcard⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension_exists_maximal_c67fb017 L hL
  have hconn :=
    WilliamsonShmoys.planar_drawing_connected_extension_maximal_is_connected_c67fb017 H hH hV hmax
  exact ⟨H, hLH, hconn, hH, hcard⟩
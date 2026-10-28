-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_connected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:28:34.525557+00:00
-- url     : https://prove2.me/submissions/3a5d2914-6c3c-4659-9867-6fc85c823019
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_disconnected_has_drawable_strict_supergraph__p2m_85d53c0c_737c_477f_b1f6_79b2d9e304de_a1

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ M : SimpleGraph V,
      K ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = K)
    (hCard : 3 ≤ Fintype.card V) :
    K.Connected := by
  by_contra hNot
  obtain ⟨M, hKM, hMDraw, hMK⟩ :=
    WilliamsonShmoys.planar_disconnected_has_drawable_strict_supergraph__p2m_85d53c0c_737c_477f_b1f6_79b2d9e304de_a1
      K hDraw (by omega) hNot
  exact hMK (hMax M hKM hMDraw)
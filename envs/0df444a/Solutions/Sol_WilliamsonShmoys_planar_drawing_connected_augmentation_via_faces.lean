-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_augmentation_via_faces
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:03:57.231088+00:00
-- url     : https://prove2.me/submissions/c2b50012-b96d-44a2-8d2e-1f3d628927e9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_augmentation_maximal_drawable_supergraph
import Theorems.Thm_WilliamsonShmoys_augmentation_maximal_drawable_connected

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hdraw : HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V, HasPlanarDrawingOn H ∧ H.Connected ∧
      G.edgeSet.ncard <= H.edgeSet.ncard := by
  obtain ⟨H, hHdraw, hGH, hmax, hcard⟩ :=
    WilliamsonShmoys.augmentation_maximal_drawable_supergraph G hdraw hV
  exact ⟨H, hHdraw,
    WilliamsonShmoys.augmentation_maximal_drawable_connected H hHdraw hV hmax,
    hcard⟩
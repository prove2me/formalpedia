-- Prove2me | solution 1 for WilliamsonShmoys.exists_drawable_edge_augmentation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:56:28.487143+00:00
-- url     : https://prove2.me/submissions/9c92fdd3-439d-44aa-bf69-a5418c998c38
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_completion
import Theorems.Thm_WilliamsonShmoys_extract_one_edge_from_drawable_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hE : G.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = G.edgeSet.ncard + 1 := by
  obtain ⟨H, hGH, hHD, _hmax, hcard⟩ :=
    WilliamsonShmoys.exists_maximal_planar_completion G hV hG
  have hneq : G ≠ H := by
    intro heq
    subst H
    omega
  exact WilliamsonShmoys.extract_one_edge_from_drawable_extension
    G H hGH hHD hneq
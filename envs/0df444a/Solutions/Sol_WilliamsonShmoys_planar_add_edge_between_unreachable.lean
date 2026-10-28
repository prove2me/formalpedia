-- Prove2me | solution 1 for WilliamsonShmoys.planar_add_edge_between_unreachable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T07:30:11.349845+00:00
-- url     : https://prove2.me/submissions/24251960-b60a-4f62-b07d-5d5d2a2174b4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_unreachable_drawing
import Theorems.Thm_WilliamsonShmoys_single_edge_extension_has_strict_edgeSet

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (u v : V)
    (hUV : ¬ K.Reachable u v) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊂ L.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by
  obtain ⟨L, hAdj, hPlanar⟩ :=
    WilliamsonShmoys.planar_add_edge_between_unreachable_drawing K hK u v hUV
  exact ⟨L,
    WilliamsonShmoys.single_edge_extension_has_strict_edgeSet K L u v hUV hAdj,
    hPlanar⟩
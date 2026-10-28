-- Prove2me | solution 1 for WilliamsonShmoys.planar_cut_edge_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:56:48.972226+00:00
-- url     : https://prove2.me/submissions/eb309868-6a93-4aa6-a30b-8a1b7bc0f5fc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_cut_separates_reachable
import Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_unreachable

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (A : Set V)
    (hCut : ∀ ⦃x y : V⦄, x ∈ A → y ∉ A → ¬ K.Adj x y)
    (u v : V)
    (hu : u ∈ A)
    (hv : v ∉ A) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊂ L.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by
  apply WilliamsonShmoys.planar_add_edge_between_unreachable K hK u v
  exact WilliamsonShmoys.planar_cut_separates_reachable K A hCut u v hu hv

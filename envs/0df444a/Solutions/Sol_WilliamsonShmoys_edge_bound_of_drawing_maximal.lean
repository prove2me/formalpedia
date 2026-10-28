-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_of_drawing_maximal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:54:11.329575+00:00
-- url     : https://prove2.me/submissions/b2c49417-56fe-4909-9b2a-81d831aed07a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_to_edge_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ S : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn S →
      G.edgeSet ⊆ S.edgeSet →
      G.edgeSet = S.edgeSet) :
    G.edgeSet.ncard + 6 >= 3 * Fintype.card V := by
  obtain ⟨S, hS, hSub, hcount⟩ :=
    WilliamsonShmoys.planar_augmentation_to_edge_bound G hCard hG
  have hEq : G.edgeSet = S.edgeSet := hmax S hS hSub
  have hcount' : G.edgeSet.ncard + 6 = 3 * Fintype.card V := by
    simpa [hEq] using hcount
  omega
-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_maximal_edge_count_of_inclusion_maximality
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:51:21.012312+00:00
-- url     : https://prove2.me/submissions/32c85886-ece4-4a88-a4eb-59880d44f8b1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_edge_bound
import Theorems.Thm_WilliamsonShmoys_planar_drawable_strict_augmentation_below_bound

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ S : SimpleGraph V,
      (∀ {u v}, R.Adj u v → S.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn S → S = R) :
    R.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hbound := WilliamsonShmoys.planar_drawable_edge_bound R hdraw hV
  by_contra hneq
  have hlt : R.edgeSet.ncard < 3 * Fintype.card V - 6 := by omega
  obtain ⟨S, hsub, hSdraw, hSR⟩ :=
    WilliamsonShmoys.planar_drawable_strict_augmentation_below_bound
      R hdraw hV hlt
  exact hSR (hmax S hsub hSdraw)
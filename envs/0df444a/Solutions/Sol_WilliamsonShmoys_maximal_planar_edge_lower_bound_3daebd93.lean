-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound_3daebd93
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T22:48:59.425971+00:00
-- url     : https://prove2.me/submissions/266f9b92-024e-46e7-95c1-2c9eeb579b31

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_augmentable_below_maximal_bound
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : forall L : SimpleGraph V, K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> K = L) :
    3 * Fintype.card V - 6 <= K.edgeSet.ncard := by
  by_contra h
  have hsparse : K.edgeSet.ncard < 3 * Fintype.card V - 6 := Nat.lt_of_not_ge h
  obtain ⟨L, hKL, hne, hL⟩ :=
    WilliamsonShmoys.planar_graph_augmentable_below_maximal_bound K hV hK hsparse
  exact hne (hMax L hKL hL)
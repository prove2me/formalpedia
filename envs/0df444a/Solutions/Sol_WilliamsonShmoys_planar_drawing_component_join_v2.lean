-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_component_join_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:17:25.521831+00:00
-- url     : https://prove2.me/submissions/c3398c64-f714-4ea7-9d07-95cdf46d86cf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_preserving
import Theorems.Thm_WilliamsonShmoys_planar_drawing_finite_extension_completion

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      L.edgeSet ⊆ H.edgeSet ∧
      H.Connected ∧
      HasPlanarDrawingOn H := by
  exact WilliamsonShmoys.planar_drawing_finite_extension_completion
    L hLdraw
    (by
      intro K hLK hKdraw hKdisc
      exact WilliamsonShmoys.planar_drawing_add_edge_preserving
        K hKdraw hKdisc)
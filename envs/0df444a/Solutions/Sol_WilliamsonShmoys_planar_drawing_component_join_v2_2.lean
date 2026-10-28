-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_component_join_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:12:05.6633+00:00
-- url     : https://prove2.me/submissions/901216ab-7912-49ba-9d46-29ccc0ab04ab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_finite_extension_completion
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extend_disconnected_components_v3

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
      exact WilliamsonShmoys.planar_drawing_extend_disconnected_components_v3
        K hKdraw hCard hKdisc)
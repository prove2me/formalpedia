-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_drawable_has_drawable_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:48:04.777233+00:00
-- url     : https://prove2.me/submissions/89ac765b-d5fb-4ec8-9881-5bcad8e29888
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_drawable_has_nonreachable_pair
import Theorems.Thm_WilliamsonShmoys_drawable_add_edge_of_nonreachable

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn H) (hV : 3 <= Fintype.card V)
    (hdisc : ¬ H.Connected) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧ K ≠ H := by
  obtain ⟨u, v, huv⟩ :=
    WilliamsonShmoys.disconnected_drawable_has_nonreachable_pair H hV hdisc
  exact WilliamsonShmoys.drawable_add_edge_of_nonreachable H hdraw huv
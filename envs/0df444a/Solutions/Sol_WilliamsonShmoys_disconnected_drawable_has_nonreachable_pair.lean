-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_drawable_has_nonreachable_pair
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T15:37:06.615415+00:00
-- url     : https://prove2.me/submissions/1989f801-3e02-45e4-8185-82ca28be5aca

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V) (hdisc : ¬ H.Connected) :
    ∃ u v : V, ¬ H.Reachable u v := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hpre : ¬ H.Preconnected := fun h => hdisc ⟨h⟩
  simp only [SimpleGraph.Preconnected, not_forall] at hpre
  exact hpre

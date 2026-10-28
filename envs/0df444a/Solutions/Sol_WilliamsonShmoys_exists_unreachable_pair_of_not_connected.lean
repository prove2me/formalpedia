-- Prove2me | solution 1 for WilliamsonShmoys.exists_unreachable_pair_of_not_connected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T16:28:36.079426+00:00
-- url     : https://prove2.me/submissions/92a22df2-df8a-453f-b627-8820b3cc38c6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hdis : Not G.Connected) :
    Exists fun u : V => Exists fun v : V => Not (G.Reachable u v) := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hpre : ¬ G.Preconnected := fun h => hdis ⟨h⟩
  simp only [SimpleGraph.Preconnected, not_forall] at hpre
  exact hpre

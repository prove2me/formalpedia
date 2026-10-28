-- Prove2me | solution 1 for WilliamsonShmoys.exists_unreachable_pair_of_card_ge_three
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T13:23:13.218497+00:00
-- url     : https://prove2.me/submissions/f5c9d3fe-79a9-450d-9424-3eb46332cd16

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hnotConnected : ¬ P.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ P.Reachable u v := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  by_contra hc
  push_neg at hc
  apply hnotConnected
  rw [SimpleGraph.connected_iff]
  refine ⟨fun u v => ?_, hne⟩
  by_cases h : u = v
  · subst h; rfl
  · exact hc u v h

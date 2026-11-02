-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_planar_drawing_has_nonreachable_pair__p2m_e7f58e98_9faf_49a6_bc58_50960cb4a0da_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T18:51:13.811889+00:00
-- url     : https://prove2.me/submissions/af30d320-ce0b-416b-abb7-36e0d506de17

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ G.Connected) :
    ∃ u v : V, ¬ G.Reachable u v := by
  classical
  have hpos : 0 < Fintype.card V := by omega
  letI : Nonempty V := Fintype.card_pos_iff.mp hpos
  by_contra h
  apply hDisconnected
  refine ⟨?_⟩
  intro u v
  by_contra huv
  exact h ⟨u, v, huv⟩

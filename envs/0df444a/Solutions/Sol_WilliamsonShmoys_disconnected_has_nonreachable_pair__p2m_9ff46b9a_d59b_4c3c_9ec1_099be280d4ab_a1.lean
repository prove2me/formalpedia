-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_has_nonreachable_pair__p2m_9ff46b9a_d59b_4c3c_9ec1_099be280d4ab_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:38:36.773232+00:00
-- url     : https://prove2.me/submissions/add138b4-e4cc-4de3-abf1-c25b0b21f4f9

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (hcard : 2 ≤ Fintype.card V)
    (hDisconnected : ¬ G.Connected) :
    ∃ u v : V, ¬ G.Reachable u v := by
  classical
  by_contra h
  have hpos : 0 < Fintype.card V := by omega
  have hne : Nonempty V := Fintype.card_pos_iff.mp hpos
  obtain ⟨v⟩ := hne
  apply hDisconnected
  rw [G.connected_iff_exists_forall_reachable]
  exact ⟨v, fun w => by
    by_contra hnot
    exact h ⟨v, w, hnot⟩⟩
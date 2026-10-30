-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_nonreachable_vertices__p2m_cc5cc3f2_db05_4ace_b001_4997052bea6e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:22:04.379826+00:00
-- url     : https://prove2.me/submissions/12717b37-b3ba-41e0-bd65-718ed0b9858c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hconn : ¬ H.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ H.Reachable u v := by
  classical
  have hcard : 0 < Fintype.card V := by omega
  have hne : Nonempty V := Fintype.card_pos_iff.mp hcard
  have hpre : ¬ H.Preconnected := by
    intro hp
    letI : Nonempty V := hne
    exact hconn ⟨hp⟩
  obtain ⟨u, v, hnot⟩ : ∃ u v : V, ¬ H.Reachable u v := by
    simpa only [SimpleGraph.Preconnected, not_forall] using hpre
  refine ⟨u, v, ?_, hnot⟩
  intro huv
  subst v
  exact hnot SimpleGraph.Reachable.rfl
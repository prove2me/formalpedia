-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_vertices__p2m_1532c25a_65bb_404f_a90f_83fae1a22778_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:53:27.713878+00:00
-- url     : https://prove2.me/submissions/3130a7cd-812d-4164-9329-500daea7a433

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdisc : ¬ G.Connected) : ∃ u v : V, u ≠ v ∧ ¬ G.Reachable u v := by
  classical
  by_contra h
  have hreach : ∀ u v : V, u ≠ v → G.Reachable u v := by
    intro u v huv
    by_contra hnot
    exact h ⟨u, v, huv, hnot⟩
  have hpre : G.Preconnected := by
    intro u v
    by_cases huv : u = v
    · subst v
      exact SimpleGraph.Reachable.refl u
    · exact hreach u v huv
  have hpos : 0 < Fintype.card V := by omega
  haveI : Nonempty V := Fintype.card_pos_iff.mp hpos
  have hconn : G.Connected := ⟨hpre⟩
  exact hdisc hconn
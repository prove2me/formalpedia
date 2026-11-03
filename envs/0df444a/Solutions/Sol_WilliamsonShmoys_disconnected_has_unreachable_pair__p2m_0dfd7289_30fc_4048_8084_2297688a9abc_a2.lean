-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_has_unreachable_pair__p2m_0dfd7289_30fc_4048_8084_2297688a9abc_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T08:30:50.324707+00:00
-- url     : https://prove2.me/submissions/15ef7134-9726-4ed5-8e13-384f0357782f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdisc : ¬ M.Connected) :
    ∃ u v : V, ¬ M.Reachable u v := by
  classical
  by_contra hbad
  have hconn : M.Connected := by
    haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    exact ⟨fun u v => by
      by_contra hnot
      exact hbad ⟨u, v, hnot⟩⟩
  exact hdisc hconn

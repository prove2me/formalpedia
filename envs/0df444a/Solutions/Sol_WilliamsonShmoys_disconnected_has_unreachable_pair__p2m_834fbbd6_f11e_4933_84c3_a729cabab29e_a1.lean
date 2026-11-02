-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_has_unreachable_pair__p2m_834fbbd6_f11e_4933_84c3_a729cabab29e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T18:10:57.833961+00:00
-- url     : https://prove2.me/submissions/b200946e-f87b-4a5c-8dff-53920d9030fa

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdis : ¬ H.Connected) :
    ∃ u v : V, ¬ H.Reachable u v := by
  by_contra h
  have hpre : H.Preconnected := by
    intro u v
    by_contra huv
    exact h ⟨u, v, huv⟩
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hconn : H.Connected := ⟨hpre⟩
  exact hdis hconn

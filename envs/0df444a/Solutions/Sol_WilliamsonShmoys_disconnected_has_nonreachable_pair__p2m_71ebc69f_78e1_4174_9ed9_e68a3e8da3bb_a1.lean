-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_has_nonreachable_pair__p2m_71ebc69f_78e1_4174_9ed9_e68a3e8da3bb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T19:52:17.055248+00:00
-- url     : https://prove2.me/submissions/d45ddaf9-86d1-4ec2-9e31-67b79a6a9cf6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdisconn : ¬ N.Connected) :
    ∃ u v : V, ¬ N.Reachable u v := by
  have hpos : 0 < Fintype.card V := by omega
  letI : Nonempty V := Fintype.card_pos_iff.mp hpos
  by_contra h
  push_neg at h
  have hconn : N.Connected := { preconnected := h }
  exact hdisconn hconn
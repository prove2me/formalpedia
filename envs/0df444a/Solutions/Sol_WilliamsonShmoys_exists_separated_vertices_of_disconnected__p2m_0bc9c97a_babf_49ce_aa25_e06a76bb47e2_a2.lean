-- Prove2me | solution 1 for WilliamsonShmoys.exists_separated_vertices_of_disconnected__p2m_0bc9c97a_babf_49ce_aa25_e06a76bb47e2_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:26:57.330188+00:00
-- url     : https://prove2.me/submissions/ee7fb7b1-fccb-42c6-bf3b-1fcb65efc01c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hdisc : Not G.Connected) :
    Exists fun u : V => Exists fun v : V => And (Not (u = v)) (Not (G.Reachable u v)) := by
  classical
  have hnonempty : Nonempty V := by
    have hpos : 0 < Fintype.card V := by omega
    exact Fintype.card_pos_iff.mp hpos
  by_contra h
  letI : Nonempty V := hnonempty
  apply hdisc
  refine SimpleGraph.Connected.mk ?_
  intro u v
  by_cases huv : u = v
  case pos =>
    subst v
    exact SimpleGraph.Reachable.refl u
  case neg =>
    by_contra hreach
    exact h (Exists.intro u (Exists.intro v (And.intro huv hreach)))
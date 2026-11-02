-- Prove2me | solution 1 for WilliamsonShmoys.connected_edge_lower_bound__p2m_60d3732d_de87_4f83_bd89_d86a85290de0_a6
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T18:53:27.522094+00:00
-- url     : https://prove2.me/submissions/799333dc-9850-4224-b755-e43742f4a4b4

import Definitions.Def_PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (hconn : forall u v : V, Nonempty (J.Walk u v)) :
    Fintype.card V <= J.edgeFinset.card + 1 := by
  classical
  by_cases hV : Nonempty V
  · letI : Nonempty V := hV
    let hJ : J.Connected :=
      ⟨fun u v => (hconn u v).elim (fun w => w.reachable)⟩
    have h := hJ.card_vert_le_card_edgeSet_add_one
    simpa only [Nat.card_eq_fintype_card, J.edgeFinset_card.symm] using h
  · letI : IsEmpty V := not_nonempty_iff.mp hV
    simp

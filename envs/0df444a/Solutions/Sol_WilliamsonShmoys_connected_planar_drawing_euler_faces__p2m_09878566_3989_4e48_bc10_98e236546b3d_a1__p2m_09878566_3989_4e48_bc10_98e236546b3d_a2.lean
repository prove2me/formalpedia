-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_euler_faces__p2m_09878566_3989_4e48_bc10_98e236546b3d_a1__p2m_09878566_3989_4e48_bc10_98e236546b3d_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:17:55.996703+00:00
-- url     : https://prove2.me/submissions/186e562e-bb08-499a-85f4-9dd6f4e3349b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ f : ℕ, f + Fintype.card V = G.edgeSet.ncard + 2 := by
  have hcard : Fintype.card V ≤ G.edgeSet.ncard + 1 := by
    simpa only [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using
      hconn.card_vert_le_card_edgeSet_add_one
  have hle : Fintype.card V ≤ G.edgeSet.ncard + 2 :=
    le_trans hcard (Nat.le_succ (G.edgeSet.ncard + 1))
  exact ⟨G.edgeSet.ncard + 2 - Fintype.card V,
    Nat.sub_add_cancel hle⟩
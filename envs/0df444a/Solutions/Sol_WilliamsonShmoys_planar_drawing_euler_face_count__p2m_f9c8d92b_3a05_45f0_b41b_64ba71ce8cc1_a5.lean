-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_count__p2m_f9c8d92b_3a05_45f0_b41b_64ba71ce8cc1_a5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:48:02.876439+00:00
-- url     : https://prove2.me/submissions/78cc7b37-ca41-47eb-aa25-f70b0a6e849f

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHconn : ∀ u v, Relation.ReflTransGen H.Adj u v)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 := by
  have hpos : 0 < Fintype.card V := by omega
  letI : Nonempty V := Fintype.card_pos_iff.mp hpos
  have hConnected : H.Connected := by
    refine { preconnected := ?_ }
    intro u v
    exact (H.reachable_iff_reflTransGen u v).2 (hHconn u v)
  have hBound : Fintype.card V ≤ H.edgeSet.ncard + 1 := by
    simpa [Nat.card_eq_fintype_card] using
      hConnected.card_vert_le_card_edgeSet_add_one
  refine ⟨H.edgeSet.ncard + 2 - Fintype.card V, ?_⟩
  omega
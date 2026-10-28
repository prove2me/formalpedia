-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_formula_for_face_data
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T12:38:38.688442+00:00
-- url     : https://prove2.me/submissions/145ceb41-3153-48b6-8c38-e8124d2d9834

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hConn : forall u v, Relation.ReflTransGen J.Adj u v)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    exists f : Nat, Fintype.card V + f = J.edgeSet.ncard + 2 := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · exact ⟨J.edgeSet.ncard + 2, by simp⟩
  have hc : J.Connected := by
    rw [SimpleGraph.connected_iff]
    exact ⟨fun u v => SimpleGraph.reachable_iff_reflTransGen u v |>.mpr (hConn u v), hV⟩
  have h := hc.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h
  have h2 : (J.edgeSet).ncard = Nat.card J.edgeSet := (Nat.card_coe_set_eq _).symm
  exact ⟨J.edgeSet.ncard + 2 - Fintype.card V, by omega⟩

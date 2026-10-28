-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_euler_faces
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T13:32:20.629921+00:00
-- url     : https://prove2.me/submissions/1af91a1b-bbfd-47c9-aab1-3e7190c072cc

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hConn : forall u v, Relation.ReflTransGen J.Adj u v)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ F : ℕ, Fintype.card V + F = J.edgeSet.ncard + 2 := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · exact ⟨J.edgeSet.ncard + 2, by simp⟩
  have hcAuto : J.Connected := by
    rw [SimpleGraph.connected_iff]
    exact ⟨fun u v => by first | exact hConn u v | exact (SimpleGraph.reachable_iff_reflTransGen u v).mpr (hConn u v), hV⟩
  have h := hcAuto.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h
  have h2 : (J.edgeSet).ncard = Nat.card J.edgeSet := (Nat.card_coe_set_eq _).symm
  exact ⟨J.edgeSet.ncard + 2 - Fintype.card V, by omega⟩

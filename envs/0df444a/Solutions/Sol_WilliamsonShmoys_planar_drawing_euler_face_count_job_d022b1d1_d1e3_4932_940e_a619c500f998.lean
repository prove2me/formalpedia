-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_count_job_d022b1d1_d1e3_4932_940e_a619c500f998
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T16:27:34.654659+00:00
-- url     : https://prove2.me/submissions/c30a0a5d-d110-424d-b9f7-0666e80212d6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn


set_option autoImplicit false
open WilliamsonShmoys
theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hdraw : HasPlanarDrawingOn G) (hconn : G.Connected) : ∃ f : Nat, Fintype.card V + f = G.edgeSet.ncard + 2 := by
  classical
  have h := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h
  have h2 : (G.edgeSet).ncard = Nat.card G.edgeSet := (Nat.card_coe_set_eq _).symm
  exact ⟨G.edgeSet.ncard + 2 - Fintype.card V, by omega⟩

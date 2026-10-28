-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_euler_face_count_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T11:36:37.910865+00:00
-- url     : https://prove2.me/submissions/4ede5123-06fd-4ea6-bc50-bce534ea3213

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys
namespace WilliamsonShmoys
theorem _root_.solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hConn : G.Connected)
    (hGdraw : HasPlanarDrawingOn G) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by
  classical
  have h := hConn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h
  have h2 : (G.edgeSet).ncard = Nat.card G.edgeSet := (Nat.card_coe_set_eq _).symm
  exact ⟨G.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
end WilliamsonShmoys


-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_count__p2m_6958ede2_46bd_4413_bb7d_9bd4b5c0d4f2_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:08:50.861933+00:00
-- url     : https://prove2.me/submissions/b81e8f24-676e-4540-bed4-6cdd8d44843a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V) (hHconn : H.Connected)
    (hHplanar : HasPlanarDrawingOn H) :
    Exists fun f : Nat => Fintype.card V + f = H.edgeSet.ncard + 2 := by
  classical
  have hle : Fintype.card V <= H.edgeSet.ncard + 1 := by
    calc
      Fintype.card V = Nat.card V := Nat.card_eq_fintype_card.symm
      _ <= Nat.card H.edgeSet + 1 := hHconn.card_vert_le_card_edgeSet_add_one
      _ = H.edgeSet.ncard + 1 := by rw [Nat.card_coe_set_eq]
  refine Exists.intro (H.edgeSet.ncard + 2 - Fintype.card V) ?_
  omega
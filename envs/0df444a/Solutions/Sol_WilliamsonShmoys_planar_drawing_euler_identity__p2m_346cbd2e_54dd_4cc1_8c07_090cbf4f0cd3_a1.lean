-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_identity__p2m_346cbd2e_54dd_4cc1_8c07_090cbf4f0cd3_a1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:29:32.0347+00:00
-- url     : https://prove2.me/submissions/af941e13-8b71-44ed-9815-debb52c4020f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hConnected : M.Connected)
    (hM : HasPlanarDrawingOn M) :
    ∃ f : ℕ, Fintype.card V + f = M.edgeSet.ncard + 2 := by
  have h := hConnected.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at h
  exact ⟨M.edgeSet.ncard + 2 - Fintype.card V, by omega⟩

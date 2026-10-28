-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_euler_equation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T01:02:24.673841+00:00
-- url     : https://prove2.me/submissions/20268f15-7ac7-41b3-97fc-50a922f068db

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected


set_option autoImplicit false
open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hConnected : L.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = L.edgeSet.ncard + 2 := by
  classical
  have h := hConnected.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h
  have h2 : (L.edgeSet).ncard = Nat.card L.edgeSet := (Nat.card_coe_set_eq _).symm
  exact ⟨L.edgeSet.ncard + 2 - Fintype.card V, by omega⟩

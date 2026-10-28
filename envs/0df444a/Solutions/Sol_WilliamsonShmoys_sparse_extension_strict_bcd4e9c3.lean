-- Prove2me | solution 1 for WilliamsonShmoys.sparse_extension_strict_bcd4e9c3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:51:34.788255+00:00
-- url     : https://prove2.me/submissions/ffa36b2e-7187-453b-93fc-0ca0817c8a0c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hHK : H ≤ K)
    (hcard : K.edgeSet.ncard = 3 * Fintype.card V - 6)
    (hsparse : H.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ¬ K.edgeSet ⊆ H.edgeSet := by
  intro hKH
  have hle : K.edgeSet.ncard ≤ H.edgeSet.ncard :=
    Set.ncard_le_ncard hKH (Set.toFinite H.edgeSet)
  have h6 : 6 ≤ 3 * Fintype.card V := by
    calc
      6 ≤ 3 * 3 := by decide
      _ ≤ 3 * Fintype.card V := Nat.mul_le_mul_left 3 hV
  have hcancel : (3 * Fintype.card V - 6) + 6 = 3 * Fintype.card V :=
    Nat.sub_add_cancel h6
  rw [hcard] at hle
  have hle' := Nat.add_le_add_right hle 6
  rw [hcancel] at hle'
  exact (not_lt_of_ge hle') hsparse
-- Prove2me | solution 1 for WilliamsonShmoys.component_edge_count_aggregation_piecewise_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:39:12.927778+00:00
-- url     : https://prove2.me/submissions/1c719248-e094-46d0-82da-374df0aa31d0

import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_piecewise_sum_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (C : Finset (Finset V))
    (f : Finset V → Nat)
    (hCardSum : C.sum Finset.card = Fintype.card V)
    (hPiece : ∀ S ∈ C,
      f S ≤ (if S.card < 3 then S.card / 2 else 3 * S.card - 6))
    (hV : 3 ≤ Fintype.card V) :
    C.sum f ≤ 3 * Fintype.card V - 6 := by
  exact WilliamsonShmoys.finite_piecewise_sum_bound
    (n := Fintype.card V) C Finset.card f hCardSum hPiece hV
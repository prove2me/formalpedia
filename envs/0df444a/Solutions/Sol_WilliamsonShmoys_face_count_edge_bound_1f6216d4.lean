-- Prove2me | solution 1 for WilliamsonShmoys.face_count_edge_bound_1f6216d4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:35:11.96556+00:00
-- url     : https://prove2.me/submissions/ad539dc8-e8bb-4ccb-a227-e135e1c076d0

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (F : Nat)
    (degree : Fin F → Nat)
    (heuler : Fintype.card V + F = H.edgeSet.ncard + 2)
    (hsum : (∑ f : Fin F, degree f) = 2 * H.edgeSet.ncard)
    (hdegree : ∀ f, 3 ≤ degree f) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  have hconst : (∑ f : Fin F, (3 : Nat)) = F * 3 := by
    simp
  have hfaces : (∑ f : Fin F, (3 : Nat)) ≤ ∑ f : Fin F, degree f := by
    exact Finset.sum_le_sum (fun f _ => hdegree f)
  have hmul : 3 * F ≤ 2 * H.edgeSet.ncard := by
    omega
  omega

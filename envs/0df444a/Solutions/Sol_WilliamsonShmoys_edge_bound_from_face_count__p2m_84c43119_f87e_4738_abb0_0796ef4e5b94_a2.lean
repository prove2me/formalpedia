-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_from_face_count__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:41:04.744168+00:00
-- url     : https://prove2.me/submissions/c6b23051-ec73-414f-b1a2-2eefec9c90de

import Mathlib

theorem solution (n e : Nat) (hCard : 3 ≤ n)
    (hCounts : ∃ F B : Nat, n + F = e + 2 ∧ B = 2 * e ∧ 3 * F ≤ B) :
    e ≤ 3 * n - 6 := by
  rcases hCounts with ⟨F, B, hEuler, hB, hInc⟩
  omega

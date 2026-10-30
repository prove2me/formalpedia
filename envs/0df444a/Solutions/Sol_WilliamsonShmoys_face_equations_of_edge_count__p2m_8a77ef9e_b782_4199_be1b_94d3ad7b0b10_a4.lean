-- Prove2me | solution 1 for WilliamsonShmoys.face_equations_of_edge_count__p2m_8a77ef9e_b782_4199_be1b_94d3ad7b0b10_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:44:33.734966+00:00
-- url     : https://prove2.me/submissions/e849c83f-eb09-4ba1-9b45-100458955f62

import Mathlib

theorem solution
    (n m : Nat) (hCard : 3 ≤ n) (hm : m + 6 = 3 * n) :
    ∃ f : Nat, n + f = m + 2 ∧ 3 * f = 2 * m := by
  refine ⟨2 * n - 4, ?_, ?_⟩ <;> omega
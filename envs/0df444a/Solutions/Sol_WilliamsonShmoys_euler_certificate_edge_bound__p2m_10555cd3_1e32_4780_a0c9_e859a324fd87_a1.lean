-- Prove2me | solution 1 for WilliamsonShmoys.euler_certificate_edge_bound__p2m_10555cd3_1e32_4780_a0c9_e859a324fd87_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:33:54.179447+00:00
-- url     : https://prove2.me/submissions/4685c319-0af5-46ee-a80f-dad37ca460fc

import Mathlib

theorem solution
    (n m m' f : Nat)
    (hn : 3 ≤ n)
    (hcert : m ≤ m' ∧ n + f = m' + 2 ∧ 3 * f ≤ 2 * m') :
    m ≤ 3 * n - 6 := by
  omega
-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_from_euler_data__p2m_49196ac4_b46c_446f_b424_262126b1b13c_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:29:53.502634+00:00
-- url     : https://prove2.me/submissions/f71ec499-9830-4b1e-b2f7-ddef57baefe6

import Mathlib

set_option autoImplicit false

theorem solution (n m' f : Nat) (hn : 3 <= n) (hm : n + f = m' + 2) (hf : 3 * f <= 2 * m') : m' <= 3 * n - 6 := by
  omega
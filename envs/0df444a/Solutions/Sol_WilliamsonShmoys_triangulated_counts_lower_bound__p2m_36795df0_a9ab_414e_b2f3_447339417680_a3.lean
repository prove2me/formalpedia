-- Prove2me | solution 1 for WilliamsonShmoys.triangulated_counts_lower_bound__p2m_36795df0_a9ab_414e_b2f3_447339417680_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:09:07.485535+00:00
-- url     : https://prove2.me/submissions/77564f4d-c38a-4361-b3fa-de0f359328cc

import Mathlib
set_option autoImplicit false

theorem solution (n m : Nat) (hn : 3 <= n) (f : Nat)
    (hEuler : n + f = m + 2) (htri : 3 * f = 2 * m) :
    3 * n - 6 <= m := by
  omega
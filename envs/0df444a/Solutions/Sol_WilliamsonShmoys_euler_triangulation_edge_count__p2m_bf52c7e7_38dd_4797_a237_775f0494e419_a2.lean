-- Prove2me | solution 1 for WilliamsonShmoys.euler_triangulation_edge_count__p2m_bf52c7e7_38dd_4797_a237_775f0494e419_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:48:30.40698+00:00
-- url     : https://prove2.me/submissions/0ae73fab-e179-4ea5-b886-4f450d009a8b

import Mathlib

set_option autoImplicit false

theorem solution
    (v e f : Nat) (hEuler : v + f = e + 2) (hTri : 3 * f = 2 * e) : 3 * v = e + 6 := by
  omega
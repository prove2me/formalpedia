-- Prove2me | solution 1 for WilliamsonShmoys.planar_euler_certificate_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:40:51.201282+00:00
-- url     : https://prove2.me/submissions/3dc77ccf-ee58-4ee8-9d1b-6a42e325e557

import Mathlib

set_option autoImplicit false

theorem solution
    (n m f : Nat)
    (hn : 3 ≤ n)
    (heuler : (n : Int) - (m : Int) + (f : Int) = 2)
    (hfaces : 3 * f ≤ 2 * m) :
    m ≤ 3 * n - 6 := by
  omega

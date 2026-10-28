-- Prove2me | solution 1 for WilliamsonShmoys.euler_certificate_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T22:20:56.322291+00:00
-- url     : https://prove2.me/submissions/ad93b0b2-030f-4849-9435-54e55e7ce664

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (f : ℕ)
    (hEuler : Fintype.card V + f = K.edgeSet.ncard + 2)
    (hIncidence : 3 * f = 2 * K.edgeSet.ncard) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  omega

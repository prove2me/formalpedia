-- Prove2me | solution 1 for WilliamsonShmoys.euler_certificate_of_edge_interval__p2m_de823218_b35b_47b7_9852_26ba1b994051_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:07:21.106201+00:00
-- url     : https://prove2.me/submissions/14b61302-0ca7-4121-a30d-a4145dcfdb64

import Mathlib

theorem solution
    (n m : ℕ) (hn : 3 ≤ n) (hlower : n - 2 ≤ m) (hupper : m ≤ 3 * n - 6) :
    ∃ f : ℕ, n + f = m + 2 ∧ 3 * f ≤ 2 * m := by
  refine ⟨m + 2 - n, ?_, ?_⟩
  · omega
  · omega
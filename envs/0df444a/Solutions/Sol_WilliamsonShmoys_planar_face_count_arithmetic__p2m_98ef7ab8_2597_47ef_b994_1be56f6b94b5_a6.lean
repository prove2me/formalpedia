-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_count_arithmetic__p2m_98ef7ab8_2597_47ef_b994_1be56f6b94b5_a6
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:04:24.388038+00:00
-- url     : https://prove2.me/submissions/5699faf4-d469-4929-9ed7-9d50198dbc1d

import Mathlib

set_option autoImplicit false

theorem solution {n m : Nat}
    (hdata : ∃ f : Nat, n + f = m + 2 ∧ 3 * f ≤ 2 * m)
    (hn : 3 ≤ n) : (m : Int) ≤ 3 * (n : Int) - 6 := by
  rcases hdata with ⟨f, heuler, hfaces⟩
  omega
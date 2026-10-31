-- Prove2me | solution 1 for WilliamsonShmoys.face_count_arithmetic__p2m_e194ab00_41b0_4b4f_af08_d9da373e3f16_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:03:35.73444+00:00
-- url     : https://prove2.me/submissions/503596a7-7d54-4f21-b0cc-f28cba0a6ffc

import Mathlib

set_option autoImplicit false

theorem solution (n m : ℕ) (h : 3 * n = m + 6) :
    ∃ f : ℕ, n + f = m + 2 ∧ 3 * f = 2 * m := by
  refine ⟨2 * n - 4, ?_, ?_⟩ <;> omega
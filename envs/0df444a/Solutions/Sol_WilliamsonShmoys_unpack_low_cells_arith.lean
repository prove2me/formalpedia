-- Prove2me | solution 1 for WilliamsonShmoys.unpack_low_cells_arith
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T11:46:52.872673+00:00
-- url     : https://prove2.me/submissions/c08c803b-1bf2-4339-83e8-8dc5e922b238

import Mathlib

set_option autoImplicit false

theorem solution (k b2 b3 b4 b5 b6 b7 : ℕ)
    (h2 : b2 ≤ 1) (h3 : b3 ≤ 1) (h4 : b4 ≤ 1) (h5 : b5 ≤ 1) (h6 : b6 ≤ 1) (h7 : b7 ≤ 1) :
    let P := 64 * k + 32 * b2 + 16 * b3 + 8 * b4 + 4 * b5 + 2 * b6 + b7
    P / 64 = k ∧ P % 64 / 32 = b2 ∧ P % 32 / 16 = b3 ∧ P % 16 / 8 = b4 ∧
      P % 8 / 4 = b5 ∧ P % 4 / 2 = b6 ∧ P % 2 = b7 := by
  intro P
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

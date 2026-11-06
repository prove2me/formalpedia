-- Prove2me | solution 2 for RH.Transport.Reflected.retained_kernel_quarter
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:08:47.102076+00:00
-- url     : https://prove2.me/submissions/c28c5a47-9a27-410b-a8c9-c02e60af4247

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

theorem solution (Td y : ℝ) :
    Td / 4 ≤ y / 4 + max 0 (Td - y) / 2 := by
  by_cases h : Td - y ≤ 0
  · rw [max_eq_left h]
    linarith
  · have h' : 0 ≤ Td - y := le_of_lt (lt_of_not_ge h)
    rw [max_eq_right h']
    linarith

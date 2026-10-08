-- Prove2me | solution 1 for catalans_constant_irrational
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T19:31:06.999439+00:00
-- url     : https://prove2.me/submissions/7e2c918c-0400-472d-9506-10bf2c1f85cd

import Mathlib
import Theorems.Thm_OAI_InternalCatalan_catalan_irrational

/-! Catalan's constant is irrational, from OpenAI's statement
`OAI.InternalCatalan.catalan_irrational`; the two series differ only in how the denominator
is cast. -/

theorem plain_series_eq_oai_series :
    (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) =
      ∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2 := by
  push_cast
  rfl

theorem solution :
    Irrational (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) := by
  rw [plain_series_eq_oai_series]
  exact OAI.InternalCatalan.catalan_irrational

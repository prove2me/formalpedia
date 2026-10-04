-- Prove2me | solution 1 for OddPerfectNumber.Kernel.dris_five_square_dvd_three_of_euler
-- status  : ACCEPTED   (disprove)
-- author  : @os0xcom
-- created : 2026-10-03T15:45:34.89585+00:00
-- url     : https://prove2.me/submissions/2301a83c-e731-48d1-ba2f-929aa6c0cf43

import Mathlib

set_option linter.unusedVariables false

theorem solution :
    ¬ (∀ (p m s : Nat) (_hp : p.Prime) (_hp2 : p != 2) (_hs : s != 0)
        (_h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s), 3 ∣ m) := by
  intro h
  have hnot : ¬ 3 ∣ 182 := by decide
  exact hnot (h 3 182 182 (by decide) (by decide) (by decide) (by decide))

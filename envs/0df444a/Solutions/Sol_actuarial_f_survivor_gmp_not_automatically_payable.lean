-- Prove2me | solution 1 for actuarial_f_survivor_gmp_not_automatically_payable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:00:55.237005+00:00
-- url     : https://prove2.me/submissions/00971c35-a3dd-4242-9622-1950d54cb84e

import Mathlib
import Definitions.Def_actuarial_f_gmpSurvivorMinimumAtPayment
open ActuarialUnderpinsF

theorem solution
    (z i t : ℕ) (dateOf : ℕ → ℕ)
    (qualifies : ℕ → ℕ → Bool)
    (survivorPre88 survivorPost88 : ℕ → ℕ → ℝ)
    (orderRate : ℕ → ℝ)
    (h : qualifies z i = false) :
    gmpSurvivorMinimumAtPayment z i t dateOf qualifies
      survivorPre88 survivorPost88 orderRate = 0 := by
  simp [gmpSurvivorMinimumAtPayment, h]

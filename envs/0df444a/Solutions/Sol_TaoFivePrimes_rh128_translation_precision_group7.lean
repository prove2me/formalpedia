-- Prove2me | solution 1 for TaoFivePrimes.rh128_translation_precision_group7
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:11:33.525563+00:00
-- url     : https://prove2.me/submissions/db0f6096-674b-4159-b3ef-f09f453f3e84

import Definitions.Def_TaoFivePrimes_RH336TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH128RoundedCoefficients14
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ n : Fin 5,
    let k := 35+n.val
    (if k<22 then (1:ℤ) else if k<25 then 5 else if k<30 then 10^4 else 10^10) *
      |(10^14:ℤ)*RH336TranslationArithmetic.numerator 256 (10^41) k-
        TaoFivePrimes_RH128RoundedCoefficients14.getD k 0*(RH336TranslationArithmetic.denominator:ℤ)| ≤
          (RH336TranslationArithmetic.denominator:ℤ) := by
  intro n
  fin_cases n <;> decide +kernel

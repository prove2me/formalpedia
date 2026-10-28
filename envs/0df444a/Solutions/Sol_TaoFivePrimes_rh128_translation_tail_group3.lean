-- Prove2me | solution 1 for TaoFivePrimes.rh128_translation_tail_group3
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:12:07.058627+00:00
-- url     : https://prove2.me/submissions/ceef3c38-17ba-4bb8-ad11-30e46cd296e5

import Definitions.Def_TaoFivePrimes_RH336TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH128RoundedCoefficients14
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ n : Fin 5,
    (10^32:ℤ)*|RH336TranslationArithmetic.numerator 256 (10^41) (55+n.val)| ≤
      (RH336TranslationArithmetic.denominator:ℤ) := by
  intro n
  fin_cases n <;> decide +kernel

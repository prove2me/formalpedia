-- Prove2me | solution 1 for TaoFivePrimes.rh128_translation_tail_group2
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:11:58.687877+00:00
-- url     : https://prove2.me/submissions/138fcb00-6984-4b3c-96ba-8609584c8dbb

import Definitions.Def_TaoFivePrimes_RH336TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH128RoundedCoefficients14
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ n : Fin 5,
    (10^32:ℤ)*|RH336TranslationArithmetic.numerator 256 (10^41) (50+n.val)| ≤
      (RH336TranslationArithmetic.denominator:ℤ) := by
  intro n
  fin_cases n <;> decide +kernel

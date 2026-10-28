-- Prove2me | solution 1 for TaoFivePrimes.rh124p5_translation_tail_group0
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:48:32.616034+00:00
-- url     : https://prove2.me/submissions/886b98b8-dec7-4f23-ab8a-b4dce5205592

import Definitions.Def_TaoFivePrimes_RH320TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH124p5RoundedCoefficients14
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ n : Fin 5,
    (10^32:ℤ)*|RH320TranslationArithmetic.numerator 249 (10^40) (40+n.val)| ≤
      (RH320TranslationArithmetic.denominator:ℤ) := by
  intro n
  fin_cases n <;> decide +kernel

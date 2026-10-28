-- Prove2me | solution 1 for TaoFivePrimes.rh124p5_translation_tail_group2
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:48:51.664126+00:00
-- url     : https://prove2.me/submissions/ed6c4981-736c-4721-a952-3412e2e79302

import Definitions.Def_TaoFivePrimes_RH320TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH124p5RoundedCoefficients14
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ n : Fin 5,
    (10^32:ℤ)*|RH320TranslationArithmetic.numerator 249 (10^40) (50+n.val)| ≤
      (RH320TranslationArithmetic.denominator:ℤ) := by
  intro n
  fin_cases n <;> decide +kernel

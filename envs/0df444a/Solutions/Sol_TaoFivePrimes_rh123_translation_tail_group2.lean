-- Prove2me | solution 1 for TaoFivePrimes.rh123_translation_tail_group2
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:36:30.089062+00:00
-- url     : https://prove2.me/submissions/f6c07a98-025c-4b70-932f-749e331086c5

import Definitions.Def_TaoFivePrimes_RH320TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH123RoundedCoefficients12
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ n : Fin 5,
    (10^32:ℤ)*|RH320TranslationArithmetic.numerator 246 (10^40) (50+n.val)| ≤
      (RH320TranslationArithmetic.denominator:ℤ) := by
  intro n
  fin_cases n <;> decide +kernel

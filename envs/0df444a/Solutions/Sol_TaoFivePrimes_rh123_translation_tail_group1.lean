-- Prove2me | solution 1 for TaoFivePrimes.rh123_translation_tail_group1
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:36:28.869414+00:00
-- url     : https://prove2.me/submissions/f71a2afe-0472-40cc-ba47-8f8d658e8ed0

import Definitions.Def_TaoFivePrimes_RH320TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH123RoundedCoefficients12
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ n : Fin 5,
    (10^32:ℤ)*|RH320TranslationArithmetic.numerator 246 (10^40) (45+n.val)| ≤
      (RH320TranslationArithmetic.denominator:ℤ) := by
  intro n
  fin_cases n <;> decide +kernel

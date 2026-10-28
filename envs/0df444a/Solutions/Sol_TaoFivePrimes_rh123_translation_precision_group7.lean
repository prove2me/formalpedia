-- Prove2me | solution 1 for TaoFivePrimes.rh123_translation_precision_group7
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:36:26.429322+00:00
-- url     : https://prove2.me/submissions/054dc601-8a4b-44b3-a262-90c27913b6a2

import Definitions.Def_TaoFivePrimes_RH320TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH123RoundedCoefficients12
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ n : Fin 5,
    let k := 35+n.val
    (if k<20 then (1:ℤ) else if k<25 then 10 else if k<30 then 10^4 else 10^8) *
      |(10^12:ℤ)*RH320TranslationArithmetic.numerator 246 (10^40) k-
        TaoFivePrimes_RH123RoundedCoefficients12.getD k 0*(RH320TranslationArithmetic.denominator:ℤ)| ≤
          (RH320TranslationArithmetic.denominator:ℤ) := by
  intro n
  fin_cases n <;> decide +kernel

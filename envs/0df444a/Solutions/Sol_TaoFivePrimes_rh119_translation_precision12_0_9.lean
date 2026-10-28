-- Prove2me | solution 1 for TaoFivePrimes.rh119_translation_precision12_0_9
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T20:32:05.89215+00:00
-- url     : https://prove2.me/submissions/92da9d51-69bf-467b-8c45-ae69ddc9d50f

import Definitions.Def_TaoFivePrimes_RH304TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH119RoundedCoefficients12
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ n : Fin 10,
    let k := 0+n.val
    (if k<20 then (1:ℤ) else if k<25 then 10
      else if k<30 then 10^4 else 10^8) *
      |(10^12:ℤ)*RH304TranslationArithmetic.numerator 238 (10^38) k-
        TaoFivePrimes_RH119RoundedCoefficients12.getD k 0*(RH304TranslationArithmetic.denominator:ℤ)| ≤
          (RH304TranslationArithmetic.denominator:ℤ) := by
  intro n
  fin_cases n <;> decide +kernel

-- Prove2me | solution 1 for TaoFivePrimes.rh119_translation_precision12_30_39
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T20:32:08.925228+00:00
-- url     : https://prove2.me/submissions/78e3cc4a-0b69-43ad-87ec-556b7d0af576

import Definitions.Def_TaoFivePrimes_RH304TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH119RoundedCoefficients12
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ n : Fin 10,
    let k := 30+n.val
    (if k<20 then (1:ℤ) else if k<25 then 10
      else if k<30 then 10^4 else 10^8) *
      |(10^12:ℤ)*RH304TranslationArithmetic.numerator 238 (10^38) k-
        TaoFivePrimes_RH119RoundedCoefficients12.getD k 0*(RH304TranslationArithmetic.denominator:ℤ)| ≤
          (RH304TranslationArithmetic.denominator:ℤ) := by
  intro n
  fin_cases n <;> decide +kernel

-- Prove2me | solution 1 for TaoFivePrimes.rh124p5_translation_precision_group0
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:47:29.667827+00:00
-- url     : https://prove2.me/submissions/0a601198-726d-4796-9911-191add557f88

import Definitions.Def_TaoFivePrimes_RH320TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH124p5RoundedCoefficients14
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ n : Fin 5,
    let k := 0+n.val
    (if k<22 then (1:ℤ) else if k<25 then 10 else if k<30 then 10^4 else 10^10) *
      |(10^14:ℤ)*RH320TranslationArithmetic.numerator 249 (10^40) k-
        TaoFivePrimes_RH124p5RoundedCoefficients14.getD k 0*(RH320TranslationArithmetic.denominator:ℤ)| ≤
          (RH320TranslationArithmetic.denominator:ℤ) := by
  intro n
  fin_cases n <;> decide +kernel

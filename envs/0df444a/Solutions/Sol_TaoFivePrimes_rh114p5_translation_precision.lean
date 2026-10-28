-- Prove2me | solution 1 for TaoFivePrimes.rh114p5_translation_precision
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:53:34.635395+00:00
-- url     : https://prove2.me/submissions/d9c18cb1-5a26-43e4-9808-2e42d5362aea

/- Exact tiered translation certificate at height 114.5. The analytic
Mellin foundations are due to sometik179 and Gabewhigham. -/
import Definitions.Def_TaoFivePrimes_RH304TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH114p5RoundedCoefficients
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ n : Fin 40,
    (if n.val<20 then (1:ℤ) else if n.val<25 then 1000
      else if n.val<30 then 10^8 else 10^12) *
      |(10^8:ℤ)*RH304TranslationArithmetic.numerator 229 (10^37) n.val-
        TaoFivePrimes_RH114p5RoundedCoefficients.getD n.val 0*(RH304TranslationArithmetic.denominator:ℤ)| ≤
          (RH304TranslationArithmetic.denominator:ℤ) := by
  decide +kernel

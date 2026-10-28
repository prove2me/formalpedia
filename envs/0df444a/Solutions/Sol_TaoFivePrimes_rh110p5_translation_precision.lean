-- Prove2me | solution 1 for TaoFivePrimes.rh110p5_translation_precision
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:20:52.157133+00:00
-- url     : https://prove2.me/submissions/76c6262e-ec68-45ff-9394-9318349e2ca9

/- Exact tiered translation certificate at height 110.5. The analytic
Mellin foundations are due to sometik179 and Gabewhigham. -/
import Definitions.Def_TaoFivePrimes_RH272TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH110p5RoundedCoefficients
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ n : Fin 40,
    (if n.val<20 then (1:ℤ) else if n.val<25 then 1000
      else if n.val<30 then 10^8 else 10^12) *
      |(10^8:ℤ)*RH272TranslationArithmetic.numerator 221 (10^36) n.val-
        TaoFivePrimes_RH110p5RoundedCoefficients.getD n.val 0*(RH272TranslationArithmetic.denominator:ℤ)| ≤
          (RH272TranslationArithmetic.denominator:ℤ) := by
  decide +kernel

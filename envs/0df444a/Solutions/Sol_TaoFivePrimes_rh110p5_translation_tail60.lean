-- Prove2me | solution 1 for TaoFivePrimes.rh110p5_translation_tail60
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:20:52.18693+00:00
-- url     : https://prove2.me/submissions/ad0ace5a-3cba-4016-ae89-18e0cce7214c

/- Exact bounds for translated moment coefficients of degrees 40--59. -/
import Definitions.Def_TaoFivePrimes_RH272TranslationArithmetic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ n : Fin 20,
    (10^32:ℤ)*|RH272TranslationArithmetic.numerator 221 (10^36) (n.val+40)| ≤
      (RH272TranslationArithmetic.denominator:ℤ) := by
  decide +kernel

-- Prove2me | solution 1 for TaoFivePrimes.rh114p5_translation_tail60
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:53:35.863682+00:00
-- url     : https://prove2.me/submissions/d3d29972-5b49-4f09-bd88-a54ac791c830

/- Exact bounds for translated moment coefficients of degrees 40--59. -/
import Definitions.Def_TaoFivePrimes_RH304TranslationArithmetic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ n : Fin 20,
    (10^32:ℤ)*|RH304TranslationArithmetic.numerator 229 (10^37) (n.val+40)| ≤
      (RH304TranslationArithmetic.denominator:ℤ) := by
  decide +kernel

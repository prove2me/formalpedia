-- Prove2me | solution 1 for TaoFivePrimes.rh119_translation_tail60
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T20:24:54.999452+00:00
-- url     : https://prove2.me/submissions/6a6b3aeb-bb17-4d45-bdbc-877cc4b58774

/- Exact bounds for translated moment coefficients of degrees 40--59. -/
import Definitions.Def_TaoFivePrimes_RH304TranslationArithmetic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ n : Fin 20,
    (10^32:ℤ)*|RH304TranslationArithmetic.numerator 238 (10^38) (n.val+40)| ≤
      (RH304TranslationArithmetic.denominator:ℤ) := by
  decide +kernel

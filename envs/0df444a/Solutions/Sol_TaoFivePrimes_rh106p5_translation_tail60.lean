-- Prove2me | solution 1 for TaoFivePrimes.rh106p5_translation_tail60
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T18:23:16.679609+00:00
-- url     : https://prove2.me/submissions/13da1129-6dbe-477a-86ac-76100e0e0d27

/- Exact tail bounds for the local xi coefficients translated from the
published 256 Mellin moments by sometik179 and Gabewhigham. -/
import Definitions.Def_TaoFivePrimes_RH101To102TranslationCertificate
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ n : Fin 20,
    (10^28:ℤ)*|RHLocalTranslationArithmetic.numerator 213 (10^35) (n.val+40)| ≤
      (RHLocalTranslationArithmetic.denominator:ℤ) := by
  decide +kernel

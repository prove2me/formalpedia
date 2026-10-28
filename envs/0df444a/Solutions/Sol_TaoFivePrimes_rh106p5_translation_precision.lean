-- Prove2me | solution 1 for TaoFivePrimes.rh106p5_translation_precision
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T18:12:29.317713+00:00
-- url     : https://prove2.me/submissions/cc99003b-a2d6-4964-ada3-0f7fc4101d85

/- Exact tiered residual bounds for the existing height-106.5 coefficient data.
The moments and translation method come from the published Prove2Me data
by sometik179, with theta/Mellin foundations by Gabewhigham. -/
import Definitions.Def_TaoFivePrimes_RH101To102TranslationCertificate
import Definitions.Def_TaoFivePrimes_RH106To107RoundedCoefficients

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ n : Fin 40,
    (if n.val < 20 then (1:ℤ) else if n.val < 25 then 1000
      else if n.val < 30 then 10^8 else 10^12) *
      |(10^8:ℤ)*RHLocalTranslationArithmetic.numerator 213 (10^35) n.val-
        (TaoFivePrimes_RH106To107RoundedCoefficients.getD n.val 0)*
          (RHLocalTranslationArithmetic.denominator:ℤ)| ≤
            (RHLocalTranslationArithmetic.denominator:ℤ) := by
  decide +kernel

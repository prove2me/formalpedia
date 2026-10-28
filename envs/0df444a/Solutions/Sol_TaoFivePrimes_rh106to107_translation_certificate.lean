-- Prove2me | solution 1 for TaoFivePrimes.rh106to107_translation_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T17:48:50.995223+00:00
-- url     : https://prove2.me/submissions/8dc64436-2186-408f-a72e-7631c800e244

import Definitions.Def_TaoFivePrimes_RH101To102TranslationCertificate
import Definitions.Def_TaoFivePrimes_RH106To107RoundedCoefficients

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution :
    RHLocalTranslationArithmetic.Valid 213 (10^35) 40
      TaoFivePrimes_RH106To107RoundedCoefficients := by
  decide +kernel

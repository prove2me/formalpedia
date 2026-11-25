-- Prove2me | solution 1 for PI.PrimesDyadicRS.W.claim_of_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:12:15.635504+00:00
-- url     : https://prove2.me/submissions/1d33019a-c5ec-4294-adc0-fb3fa62f4ed4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PrimesDyadicRS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_ThetaDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_FloorHalf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_ClaimOfTwo
import Theorems.Thm_PI_PrimesDyadicRS_W_thetaDiff
import Theorems.Thm_PI_PrimesDyadicRS_W_psiTheta
import Theorems.Thm_PI_PrimesDyadicRS_W_claim_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PrimesDyadicRS PI.PrimesDyadicRS.W
namespace PI.PrimesDyadicRS.W
theorem _root_.solution (hS : SmallNat) (hR : RealIneq) : PI.PrimesDyadicRS.Claim :=
  claim_of hS thetaDiff psiTheta hR
end PI.PrimesDyadicRS.W

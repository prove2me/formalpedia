-- Prove2me | solution 1 for PI.OpWords.pairingDivisibility
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:31:49.123222+00:00
-- url     : https://prove2.me/submissions/533700e7-8826-43d7-9027-f16cf5a5ed8a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_IsWeightedHomogeneousPairingLeft
import Theorems.Thm_PI_OpWords_WeightedHomogeneousPolynomialDifferentialWords_divT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace PI.OpWords
theorem _root_.solution : PI.OpWords.DivT := PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.divT
end PI.OpWords

-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_operators_commute_translations__00a6043da29f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:07:25.378422+00:00
-- url     : https://prove2.me/submissions/5deb8260-6fff-4be6-b832-79c2ae2f6640

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_AAInvTrans
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IsotropicNormalFormPartial
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorsCommuteTranslations
import Theorems.Thm_operators_commute_translations


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.C3.OperatorsCommuteTranslations := operators_commute_translations
end Formalism.FourierDecayAlt.P

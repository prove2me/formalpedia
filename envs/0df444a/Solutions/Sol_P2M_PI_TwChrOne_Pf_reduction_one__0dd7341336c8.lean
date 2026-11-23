-- Prove2me | solution 1 for P2M_PI_TwChrOne_Pf_reduction_one__0dd7341336c8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:28.359302+00:00
-- url     : https://prove2.me/submissions/aa430cd6-576c-48c4-9df9-b07fc7a43b2e

import Definitions.Def_Formalism_PeriodIntegrals_TwChrOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedCharacterOne_IsIntegralAtSuperdiagonalSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwChrOne PI.TwChrOne.Pf
variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))
namespace PI.TwChrOne.Pf
theorem _root_.solution : redP P (1 : E) = 1 := (redH P).map_one
end PI.TwChrOne.Pf

-- Prove2me | solution 1 for chk_discFactor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:02:44.650658+00:00
-- url     : https://prove2.me/submissions/b505382d-6310-41d8-bd3f-7126bc5ee828

import Definitions.Def_Formalism_PeriodIntegrals_DiscIn
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindowIn
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LandauLocal3
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LRight
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZetaGrowth
import Definitions.Def_Formalism_PeriodIntegrals_ExplicitFormulaCounts_AnalyticInputs
import Theorems.Thm_Formalism_ZF_zeroFactorization


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.DiscFactor := Formalism.ZF.zeroFactorization

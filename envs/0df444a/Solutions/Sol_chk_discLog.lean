-- Prove2me | solution 1 for chk_discLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:02:46.956896+00:00
-- url     : https://prove2.me/submissions/351be087-6e1a-4de0-8b9c-1cc0bfe026be

import Definitions.Def_Formalism_PeriodIntegrals_DiscIn
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindowIn
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LandauLocal3
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LRight
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZetaGrowth
import Definitions.Def_Formalism_PeriodIntegrals_ExplicitFormulaCounts_AnalyticInputs
import Theorems.Thm_Formalism_ZF_zflb_exists_log


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.DiscLog := fun _ _ _ hf hne => Formalism.ZF.zflb_exists_log hf hne

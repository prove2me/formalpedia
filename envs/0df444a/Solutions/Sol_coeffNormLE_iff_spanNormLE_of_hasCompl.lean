-- Prove2me | solution 1 for coeffNormLE_iff_spanNormLE_of_hasCompl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:02:49.285163+00:00
-- url     : https://prove2.me/submissions/596b48ea-f22c-4f26-b407-2b08e5a5e8a3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NablaSpans_MinorProdSpanHasCompl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_GenFrameSBOfSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_BasisMonomialsApply
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_GenFrameSB
import Theorems.Thm_GenFrameSpan_genFrameSB_of_span
import Theorems.Thm_GenFrameSpan_stepSpan


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : CutKW.KWsb := GenFrameSpan.genFrameSB_of_span GenFrameSpan.stepSpan

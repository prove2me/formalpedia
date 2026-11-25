-- Prove2me | solution 1 for P2M_rtt_independence__b8a1513eb9c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:39:08.226432+00:00
-- url     : https://prove2.me/submissions/2afcb592-2784-47d0-bb1d-a21ec75fcfb5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuarticIndependence_QmIndep
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmIndep
import Theorems.Thm_PI_QmIndepW_qmIndep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.RTTIndependence := PI.QmIndepW.qmIndep

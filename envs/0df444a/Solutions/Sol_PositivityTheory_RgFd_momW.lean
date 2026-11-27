-- Prove2me | solution 1 for PositivityTheory.RgFd.momW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:21:20.344304+00:00
-- url     : https://prove2.me/submissions/453b9344-ed3f-413c-85e6-22cec86c7898

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_FormalDegree_FormalDegreeHilbert_MomB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_FormalDegree_FormalDegreeHilbert_MomentRecursion_MomStep
import Theorems.Thm_PositivityTheory_RgFd_momA
import Theorems.Thm_PositivityTheory_RgFd_momB
import Theorems.Thm_PositivityTheory_RgFd_momW_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open PositivityTheory PositivityTheory.RgFd
namespace PositivityTheory.RgFd
theorem _root_.solution : MomW := momW_of momA momB
end PositivityTheory.RgFd

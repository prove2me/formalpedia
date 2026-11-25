-- Prove2me | solution 1 for PositivityTheory.RgTw.th_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:56:30.511458+00:00
-- url     : https://prove2.me/submissions/d83aa3c7-5c50-4d23-b49c-ee0562b15268

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_DiscreteSeriesTopClasses_IsMQEmpty
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_DiscreteSeriesTopClasses_IsInvOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.RgTw
variable {n : ℕ}
namespace PositivityTheory.RgTw
theorem _root_.solution : th (1 : G n) = 1 := by simp [th]
end PositivityTheory.RgTw

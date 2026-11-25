-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesIdealIndexPos_toOne_injective_1a42c0d39bbb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:00:46.379604+00:00
-- url     : https://prove2.me/submissions/48ccb8ef-92fe-4029-bf6a-13192e098bfb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesIdealIndexPos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
open scoped nonZeroDivisors
open GroundTheory.Heights₂.Heights.KLinesIdealIndexPos
variable {K : Type} [Field K] [NumberField K]
omit [NumberField K]
namespace GroundTheory.Heights₂.Heights.KLinesIdealIndexPos
theorem _root_.solution : Function.Injective (toOne K) := fun _ _ h =>
  congrFun h ()
end GroundTheory.Heights₂.Heights.KLinesIdealIndexPos

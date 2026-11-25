-- Prove2me | solution 1 for P2M_GroundTheory_Automorphic_LineKernel_hasCompactSupport_conv__C_94b8ee077835
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:34:16.482328+00:00
-- url     : https://prove2.me/submissions/cd1e88b4-29c5-4245-96f6-d7fe76927979

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_hasCompactSupport__C_147c0388f3f8
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_hasCompactSupport_KC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
variable {a r : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hr : ∀ j, 0 < r j)
include ha hr
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution (n : ℕ) :
    HasCompactSupport (KC a r n ⋆[mul ℂ ℂ] ηC a r (n + 1)) :=
  (hasCompactSupport_KC ha hr n).convolution (mul ℂ ℂ) (hasCompactSupport_ηC ha hr _)
end GroundTheory.Automorphic.LineKernel

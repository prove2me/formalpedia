-- Prove2me | solution 1 for P2M_GroundTheory_Automorphic_LineKernel_contDiff_conv__C_0b797dd792e8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:29:27.888612+00:00
-- url     : https://prove2.me/submissions/e855c3e9-1141-498e-a904-a9034eb78264

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_contDiff__C_d6b9b6ae5dcf
import Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_hasCompactSupport__C_147c0388f3f8
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integrable_KC

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
theorem _root_.solution (n : ℕ) : ContDiff ℝ ∞ (KC a r n ⋆[mul ℂ ℂ] ηC a r (n + 1)) := by
  have e : (KC a r n ⋆[mul ℂ ℂ] ηC a r (n + 1)) = (KC a r n ⋆[mul ℝ ℂ] ηC a r (n + 1)) := by
    funext x; simp only [convolution_def, mul_apply']
  rw [e]
  exact (hasCompactSupport_ηC ha hr _).contDiff_convolution_right (mul ℝ ℂ)
    (integrable_KC ha hr n).locallyIntegrable (contDiff_ηC a r _)
end GroundTheory.Automorphic.LineKernel

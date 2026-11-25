-- Prove2me | solution 1 for P2M_GroundTheory_Automorphic_LineKernel_contDiff___70b804dc509f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:38:16.05467+00:00
-- url     : https://prove2.me/submissions/764185be-28a6-4a84-aa29-4ec15a5d6f85

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_contDiff_iteratedDeriv_of_contDiff
import Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_contDiff__C_d6b9b6ae5dcf
import Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_contDiff_conv__C_0b797dd792e8


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
open scoped ContDiff Convolution Pointwise FourierTransform
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
variable {a r : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hr : ∀ j, 0 < r j)
include ha hr
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution (n : ℕ) : ContDiff ℝ ∞ (ρ a r n) := by
  cases n with
  | zero => exact contDiff_ηC a r 0
  | succ n =>
    simp only [ρ]
    exact ContDiff.sum fun p _ => contDiff_const.mul
      (contDiff_iteratedDeriv_of_contDiff (contDiff_conv_ηC ha hr n) p)
end GroundTheory.Automorphic.LineKernel

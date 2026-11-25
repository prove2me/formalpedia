-- Prove2me | solution 1 for P2M_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv__C_ac13ffdbfcb3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:34:19.305952+00:00
-- url     : https://prove2.me/submissions/652c3ea0-61b9-4038-93f0-ae55c49b431b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_contDiff_rem
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_iteratedDeriv_ofReal


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
theorem _root_.solution (j q : ℕ) (t : ℝ) :
    ‖iteratedDeriv q (ηC a r j) t‖ = ‖iteratedDeriv q (rem (a j) (r j)) t‖ := by
  have := iteratedDeriv_ofReal (contDiff_rem (a j) (r j)) q
  show ‖iteratedDeriv q (fun t => ((rem (a j) (r j) t : ℝ) : ℂ)) t‖ = _
  rw [this, Complex.norm_real]
end GroundTheory.Automorphic.LineKernel

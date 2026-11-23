-- Prove2me | solution 1 for P2M_GroundTheory_Automorphic_LineKernel_contDiff__C_d6b9b6ae5dcf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:27:55.730855+00:00
-- url     : https://prove2.me/submissions/8d8d8ec7-c92f-4428-b49d-a22c763d1cd3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_contDiff_rem


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
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution (a r : ℕ → ℝ) (j : ℕ) : ContDiff ℝ ∞ (ηC a r j) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_rem _ _)
end GroundTheory.Automorphic.LineKernel

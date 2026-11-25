-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_real_inner_eq_re_69fd56d86293
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:54:16.140906+00:00
-- url     : https://prove2.me/submissions/0ddfa3d9-6068-4dcd-9f7d-d31be0590d53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFrameJacobianSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFrameJacobianSum

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
open Matrix Finset Module
noncomputable section
open GroundTheory.Heights₂.Heights.FrameJacobianSumAlt
variable {d : ℕ} {ι : Type*} [Fintype ι]
namespace GroundTheory.Heights₂.Heights.FrameJacobianSumAlt
theorem _root_.solution (x y : EuclideanSpace ℂ ι) : inner ℝ x y = (inner ℂ x y).re := by
  simp [PiLp.inner_apply, Complex.re_sum, Complex.inner]
end GroundTheory.Heights₂.Heights.FrameJacobianSumAlt

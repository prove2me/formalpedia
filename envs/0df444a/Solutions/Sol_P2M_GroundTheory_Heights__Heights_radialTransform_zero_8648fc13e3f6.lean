-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_radialTransform_zero_8648fc13e3f6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:38:18.760681+00:00
-- url     : https://prove2.me/submissions/9cc077b9-172e-4f15-ae38-aae554615aa9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegLelongAnnulus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (a : ℝ → ℝ) : radialTransform 0 a = a := by
  funext t
  simp [radialTransform]
end GroundTheory.Heights₂.Heights

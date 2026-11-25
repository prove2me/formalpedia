-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceCut_eq_one_of_lt_one_1edff12b97b4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:16:55.160212+00:00
-- url     : https://prove2.me/submissions/124b5c05-9f52-407a-87c9-006b6006430d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut

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
open MvPolynomial Filter Topology Matrix
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.SliceCut
variable {n : ℕ} (h : HermNorm n)
namespace GroundTheory.Heights₂.Heights.SliceCut
theorem _root_.solution (k : ℕ) {x : Fin n → ℂ} (hx : h.dualNorm x < 1) : sliceCut h k x = 1 := by
  unfold sliceCut
  refine Real.smoothTransition.one_of_one_le ?_
  have hlog : Real.log (h.dualNorm x) ≤ 0 := Real.log_nonpos (Real.sqrt_nonneg _) hx.le
  have : Real.log (h.dualNorm x) / ((k : ℝ) + 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hlog (by positivity)
  linarith
end GroundTheory.Heights₂.Heights.SliceCut

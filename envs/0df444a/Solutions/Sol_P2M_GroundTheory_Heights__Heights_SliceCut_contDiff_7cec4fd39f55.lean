-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceCut_contDiff_7cec4fd39f55
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:56:38.393795+00:00
-- url     : https://prove2.me/submissions/92874652-9c9a-4029-bc85-fbe046ff4a96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceCut_continuous_dualNorm_d0655469d688
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceCut_eq_one_of_lt_one_1edff12b97b4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiffOn_log_dualNorm_a92d55d266bf


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
theorem _root_.solution (k : ℕ) : ContDiff ℝ ∞ (sliceCut h k) := by
  refine contDiff_iff_contDiffAt.mpr fun x => ?_
  by_cases hx : x = 0
  · subst hx
    have hU : {y : Fin n → ℂ | h.dualNorm y < 1} ∈ 𝓝 (0 : Fin n → ℂ) := by
      refine (isOpen_lt (continuous_dualNorm h) continuous_const).mem_nhds ?_
      simp [HermNorm.dualNorm]
    exact contDiffAt_const.congr_of_eventuallyEq
      (Filter.mem_of_superset hU fun y hy => eq_one_of_lt_one h k hy)
  · have hlog := (contDiffOn_log_dualNorm h).contDiffAt (isOpen_compl_singleton.mem_nhds hx)
    exact Real.smoothTransition.contDiff.contDiffAt.comp x (contDiffAt_const.sub (hlog.div_const _))
end GroundTheory.Heights₂.Heights.SliceCut

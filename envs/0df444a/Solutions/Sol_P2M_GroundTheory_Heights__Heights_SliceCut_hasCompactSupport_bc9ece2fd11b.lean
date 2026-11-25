-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceCut_hasCompactSupport_bc9ece2fd11b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:44:00.650119+00:00
-- url     : https://prove2.me/submissions/d528be8a-78bd-476b-848b-af16301bade2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceCut_isCompact_sublevel_b5ec35a73f83

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
theorem _root_.solution (k : ℕ) : HasCompactSupport (sliceCut h k) := by
  refine HasCompactSupport.intro (isCompact_sublevel h (Real.exp (2 * ((k : ℝ) + 1)))) fun x hx => ?_
  simp only [Set.mem_ofPred_eq, not_le] at hx
  unfold sliceCut
  refine Real.smoothTransition.zero_of_nonpos ?_
  have hpos : 0 < h.dualNorm x := (Real.exp_pos _).trans hx
  have hlog : 2 * ((k : ℝ) + 1) < Real.log (h.dualNorm x) := by
    rw [Real.lt_log_iff_exp_lt hpos]; exact hx
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [sub_nonpos, le_div_iff₀ hk]
  linarith
end GroundTheory.Heights₂.Heights.SliceCut

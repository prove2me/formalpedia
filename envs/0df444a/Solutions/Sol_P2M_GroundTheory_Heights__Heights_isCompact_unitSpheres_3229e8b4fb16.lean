-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isCompact_unitSpheres_3229e8b4fb16
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:11.365071+00:00
-- url     : https://prove2.me/submissions/1d4a85ed-8ad4-4ca9-82e0-449bf5047526

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_continuous_l2Norm_de9fc54faefe

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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : IsCompact (unitSpheres n) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have : unitSpheres n = ⋂ k, {z : Cone n ℂ | l2Norm (z k) = 1} := by
      ext z; simp [unitSpheres]
    rw [this]
    exact isClosed_iInter fun k ↦
      isClosed_eq (continuous_l2Norm.comp (continuous_apply k)) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Cone n ℂ)) (r := 1)).subset fun z hz ↦ ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun k ↦
      (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i ↦ ?_
    rw [← hz k]
    exact norm_le_l2Norm (z k) i
end GroundTheory.Heights₂.Heights

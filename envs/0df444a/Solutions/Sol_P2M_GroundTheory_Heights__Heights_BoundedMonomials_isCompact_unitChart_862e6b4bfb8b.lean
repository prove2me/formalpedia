-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BoundedMonomials_isCompact_unitChart_862e6b4bfb8b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:46.976898+00:00
-- url     : https://prove2.me/submissions/e654f29c-153f-4266-83b9-039bf5850e7f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZero

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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.BoundedMonomials
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.BoundedMonomials
theorem _root_.solution (c : (k : ι) → Fin (n k + 1)) : IsCompact (unitChart c) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have h : unitChart c = (⋂ k, {z : Cone n ℂ | z k (c k) = 1}) ∩
        ⋂ k, ⋂ i, {z : Cone n ℂ | ‖z k i‖ ≤ 1} := by
      ext z
      simp [unitChart]
    rw [h]
    refine (isClosed_iInter fun k ↦ ?_).inter (isClosed_iInter fun k ↦ isClosed_iInter fun i ↦ ?_)
    · exact isClosed_eq ((continuous_apply (c k)).comp (continuous_apply k)) continuous_const
    · exact isClosed_le ((continuous_apply i).comp (continuous_apply k)).norm continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Cone n ℂ)) (r := 1)).subset fun z hz ↦ ?_
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro k
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    exact hz.2 k
end GroundTheory.Heights₂.Heights.BoundedMonomials

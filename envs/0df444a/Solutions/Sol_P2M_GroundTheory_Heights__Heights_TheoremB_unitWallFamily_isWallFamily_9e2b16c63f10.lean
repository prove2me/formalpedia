-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_unitWallFamily_isWallFamily_9e2b16c63f10
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:39.006088+00:00
-- url     : https://prove2.me/submissions/776b364b-dac8-4ed2-a41a-0e9462eaa24e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_isClosed_rootHyperplane_5ca09dd4c102

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset
variable (d : IndexData)
namespace GroundTheory.Heights₂.Heights.TheoremB
theorem _root_.solution : IsWallFamily d (unitWallFamily d) := by
  intro τ a b _
  refine ⟨(isCompact_closedBall 0 1).inter_right (isClosed_rootHyperplane d τ a b),
    Set.inter_subset_right, Metric.ball 0 1, Metric.isOpen_ball,
    ⟨0, Metric.mem_ball_self one_pos, ?_⟩, ?_⟩
  · show (0 : Weight d) (τ, a) = (0 : Weight d) (τ, b)
    rfl
  · exact Set.inter_subset_inter_left _ Metric.ball_subset_closedBall
end GroundTheory.Heights₂.Heights.TheoremB

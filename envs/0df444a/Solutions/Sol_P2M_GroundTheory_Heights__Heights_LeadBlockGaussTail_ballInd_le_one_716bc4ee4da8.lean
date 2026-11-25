-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_ballInd_le_one_716bc4ee4da8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:02:31.581601+00:00
-- url     : https://prove2.me/submissions/cf12f32a-a83a-4f41-ac97-c6bb4d02a1ee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLeadBlockGaussTail

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
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LeadBlockGaussTail
namespace GroundTheory.Heights₂.Heights.LeadBlockGaussTail
theorem _root_.solution (ρ : ℝ) (z : ℂ) : ballInd ρ z ≤ 1 := by
  unfold ballInd Set.indicator
  split_ifs <;> simp
end GroundTheory.Heights₂.Heights.LeadBlockGaussTail

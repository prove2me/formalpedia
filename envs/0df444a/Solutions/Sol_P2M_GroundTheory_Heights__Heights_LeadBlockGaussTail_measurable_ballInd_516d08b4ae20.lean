-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_measurable_ballInd_516d08b4ae20
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:03:18.635144+00:00
-- url     : https://prove2.me/submissions/d02848e8-e4aa-446f-bc99-8ff8313ba397

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
theorem _root_.solution (ρ : ℝ) : Measurable (ballInd ρ) :=
  measurable_const.indicator (measurableSet_lt (by fun_prop) measurable_const)
end GroundTheory.Heights₂.Heights.LeadBlockGaussTail

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_proof_fb2253ef6956
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:44:41.192699+00:00
-- url     : https://prove2.me/submissions/6733ee3a-a0b1-46c3-aa58-52304ebbd6d8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinGradedFrameIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_forward_756e8a607425
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_backward_52f4b24566df

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
universe u v w
open GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation
theorem _root_.solution : Statement.{u, v, w} := by
  intro o _ Ω _ _ K _ ι _ y N E _ _ B w b
  exact ⟨forward, backward⟩
end GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation

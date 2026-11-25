-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_legendreCharacter_seven_three_6f40b2ef03c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:44:39.715843+00:00
-- url     : https://prove2.me/submissions/5e73746a-81c2-4905-b844-f01bfe22b017

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open UpperHalfPlane ModularGroup ModularForm Complex NumberField
open scoped Real Modular MatrixGroups nonZeroDivisors
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution : legendreCharacter 7 3 = -1 := by
  have : quadraticChar (ZMod 7) 3 = -1 := by decide
  simp [legendreCharacter, MulChar.ringHomComp_apply, this]
end GroundTheory.Heights₂.Theta

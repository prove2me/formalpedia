-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Theta_legendreCharacter_seven_two_ad746203d57f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:13:25.039897+00:00
-- url     : https://prove2.me/submissions/c56fb173-2bb8-44dd-af63-cd9082763928

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
theorem _root_.solution : legendreCharacter 7 2 = 1 := by
  have : quadraticChar (ZMod 7) 2 = 1 := by decide
  simp [legendreCharacter, MulChar.ringHomComp_apply, this]
end GroundTheory.Heights₂.Theta

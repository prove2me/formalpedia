-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_legendreCharacter_seven_ne_one_fafc0dc76a9a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:50:44.967812+00:00
-- url     : https://prove2.me/submissions/23159e83-f961-4d22-9803-ec0e3d635ccc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_legendreCharacter_seven_three_6f40b2ef03c0

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
theorem _root_.solution : legendreCharacter 7 ≠ 1 := by
  intro h
  have h3 := legendreCharacter_seven_three
  rw [h] at h3
  have hu : IsUnit (3 : ZMod 7) := by decide
  rw [MulChar.one_apply hu] at h3
  norm_num at h3
end GroundTheory.Heights₂.Theta

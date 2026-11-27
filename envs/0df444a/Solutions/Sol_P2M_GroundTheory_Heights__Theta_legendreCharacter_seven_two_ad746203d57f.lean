-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_legendreCharacter_seven_two_ad746203d57f
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:19:13.584224+00:00
-- url     : https://prove2.me/submissions/b307ab7f-eb44-4b5f-b611-7cc5f81b9e3c

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
theorem _root_.solution : legendreCharacter 7 2 = 1 := by
  first | decide | rfl | (unfold GroundTheory.Heights₂.Theta.legendreCharacter; decide) | (simp [GroundTheory.Heights₂.Theta.legendreCharacter]; decide)




-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_LFunction_legendreCharacter_seven_one_ne_zero_c880373176f6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:10:53.934034+00:00
-- url     : https://prove2.me/submissions/30db8132-25fc-4889-8a20-32a4d59b7b80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_legendreCharacter_seven_ne_one_fafc0dc76a9a

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
theorem _root_.solution :
    DirichletCharacter.LFunction (legendreCharacter 7) 1 ≠ 0 :=
  DirichletCharacter.LFunction_apply_one_ne_zero legendreCharacter_seven_ne_one
end GroundTheory.Heights₂.Theta

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LineChowForm_substZeroOneOne_X_of_ne_0b3fd90d8c9f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:03:29.84432+00:00
-- url     : https://prove2.me/submissions/7a94c165-e9b6-49bb-85a7-f6ff773f9aa7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant

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
open GroundTheory.Heights₂.Heights.LineChowForm
variable {F : Type*} [Field F]
variable {F : Type*} [Field F]
namespace GroundTheory.Heights₂.Heights.LineChowForm
theorem _root_.solution (i : Fin 2 × Fin 2) (hi : i ≠ (1,1)) :
    substZeroOneOne (X i : MvPolynomial (Fin 2 × Fin 2) F) = X i := by
  simp [substZeroOneOne, hi]
end GroundTheory.Heights₂.Heights.LineChowForm

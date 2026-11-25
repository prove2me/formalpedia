-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LineChowForm_substZeroOneOne_X_zero_zero_8d8cd2c59b46
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:03:32.479359+00:00
-- url     : https://prove2.me/submissions/1435e4b1-179c-4c85-a6b4-9c70a9dbe46a

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
theorem _root_.solution : substZeroOneOne (X (0,0) : MvPolynomial (Fin 2 × Fin 2) F) = X (0,0) := by
  simp [substZeroOneOne]
end GroundTheory.Heights₂.Heights.LineChowForm

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LineChowForm_det_two_ne_zero_1d68ea83fc5a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:03:26.678582+00:00
-- url     : https://prove2.me/submissions/71bb58be-107a-4d0b-a20e-7109a6f8e339

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
theorem _root_.solution : (D2 : MvPolynomial (Fin 2 × Fin 2) F) ≠ 0 := by
  intro h
  have := congrArg (eval (fun ij : Fin 2 × Fin 2 => if ij.1 = ij.2 then (1 : F) else 0)) h
  simp [D2] at this
end GroundTheory.Heights₂.Heights.LineChowForm

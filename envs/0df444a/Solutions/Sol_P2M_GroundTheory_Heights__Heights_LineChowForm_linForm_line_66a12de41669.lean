-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LineChowForm_linForm_line_66a12de41669
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:51:00.563391+00:00
-- url     : https://prove2.me/submissions/67980e69-474f-4dc3-bd8d-cea19bbf2c2e

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
theorem _root_.solution : linForm (fun j : Fin 2 => if j = 0 then (1 : F) else 0) ∉
    (⊥ : Ideal (MvPolynomial (Fin 2) F)) := by
  rw [Ideal.mem_bot]
  intro h
  have := congrArg (eval (fun _ : Fin 2 => (1 : F))) h
  simp [linForm, Fin.sum_univ_two] at this
end GroundTheory.Heights₂.Heights.LineChowForm

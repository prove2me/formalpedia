-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LineChowForm_isProjPrime_line_6c88d2fbf567
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:43:28.369944+00:00
-- url     : https://prove2.me/submissions/b0a6b6f0-068d-4f03-b38d-b1cdd718cead

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
theorem _root_.solution : IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) F)) where
  isPrime := Ideal.isPrime_bot
  isHomog f hf d := by
    rw [Ideal.mem_bot] at hf ⊢
    simp [hf]
  isRelevant := ⟨0, by rw [Ideal.mem_bot]; exact X_ne_zero 0⟩
end GroundTheory.Heights₂.Heights.LineChowForm

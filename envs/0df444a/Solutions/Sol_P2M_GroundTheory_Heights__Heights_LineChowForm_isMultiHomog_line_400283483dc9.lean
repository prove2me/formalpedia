-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LineChowForm_isMultiHomog_line_400283483dc9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:03:28.289164+00:00
-- url     : https://prove2.me/submissions/4a585ea1-1994-4211-8372-b9f538c81440

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
theorem _root_.solution : IsMultiHomog 1 (D2 : MvPolynomial (Fin 2 × Fin 2) F) := by
  have hX : ∀ i j : Fin 2, IsWeightedHomogeneous (groupWeight 2 2)
      (X (i, j) : MvPolynomial (Fin 2 × Fin 2) F) (Pi.single i 1) :=
    fun i j => isWeightedHomogeneous_X F (groupWeight 2 2) (i, j)
  have hw : (Pi.single 0 1 + Pi.single 1 1 : Fin 2 → ℕ) = fun _ => 1 := by
    funext i; fin_cases i <;> simp
  have a := (hX 0 0).mul (hX 1 1)
  have b := (hX 0 1).mul (hX 1 0)
  rw [hw] at a b
  exact (weightedHomogeneousSubmodule F (groupWeight 2 2) (fun _ => 1)).sub_mem a b
end GroundTheory.Heights₂.Heights.LineChowForm

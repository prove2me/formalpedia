-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isMultiHomog_pointForm_67f7417897ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:59.545723+00:00
-- url     : https://prove2.me/submissions/7542220e-4ddc-4f9a-ae1d-c0d9c9b7a078

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDefectPoint

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
open MvPolynomial MeasureTheory Matrix
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (c : ℂ) (y : Fin n → ℂ) :
    IsMultiHomog 1 (C c * ∑ j, C (y j) * X ((0 : Fin 1), j) : MvPolynomial (Fin 1 × Fin n) ℂ) := by
  have hw : ∀ j : Fin n, groupWeight 1 n ((0 : Fin 1), j) = fun _ => 1 := by
    intro j
    funext i
    rw [Fin.fin_one_eq_zero i]
    simp [groupWeight]
  have hsum : IsWeightedHomogeneous (groupWeight 1 n)
      (∑ j, C (y j) * X ((0 : Fin 1), j) : MvPolynomial (Fin 1 × Fin n) ℂ) (fun _ => 1) := by
    rw [← mem_weightedHomogeneousSubmodule]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [mem_weightedHomogeneousSubmodule]
    have hX := isWeightedHomogeneous_X ℂ (groupWeight 1 n) ((0 : Fin 1), j)
    rw [hw j] at hX
    simpa [zero_add] using (isWeightedHomogeneous_C (groupWeight 1 n) (y j)).mul hX
  unfold IsMultiHomog
  simpa [zero_add] using (isWeightedHomogeneous_C (groupWeight 1 n) c).mul hsum
end GroundTheory.Heights₂.Heights

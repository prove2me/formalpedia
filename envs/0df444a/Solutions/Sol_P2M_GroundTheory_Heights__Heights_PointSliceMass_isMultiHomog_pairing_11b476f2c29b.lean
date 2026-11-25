-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointSliceMass_isMultiHomog_pairing_11b476f2c29b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:34.285751+00:00
-- url     : https://prove2.me/submissions/59b8e34e-a1b2-447f-bfbc-445336ae8e64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPointSliceMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointChowForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPointIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPointSliceMass

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
open GroundTheory.Heights₂.Heights.PointSliceMass
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.PointSliceMass
theorem _root_.solution (y : Fin n → ℂ) :
    IsMultiHomog 1 (∑ j, C (y j) * X ((0 : Fin 1), j) : MvPolynomial (Fin 1 × Fin n) ℂ) := by
  unfold IsMultiHomog
  refine IsWeightedHomogeneous.sum _ _ _ fun j _ => ?_
  have hX := isWeightedHomogeneous_X (R := ℂ) (groupWeight 1 n) ((0 : Fin 1), j)
  have hw : groupWeight 1 n ((0 : Fin 1), j) = fun _ => 1 := by
    funext i
    rw [Fin.fin_one_eq_zero i]
    simp [groupWeight]
  rw [hw] at hX
  simpa using (isWeightedHomogeneous_C (groupWeight 1 n) (y j)).mul hX
end GroundTheory.Heights₂.Heights.PointSliceMass

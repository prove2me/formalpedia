-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isMultiHomog_point_50a43e297f77
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:19.61683+00:00
-- url     : https://prove2.me/submissions/0f0def32-76be-43ea-819f-f8a6d7eb335a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements

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
open MvPolynomial MeasureTheory NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (R : Type*) [CommSemiring R] :
    IsMultiHomog 1 (X (0, 0) : MvPolynomial (Fin 1 × Fin 1) R) := by
  have h := isWeightedHomogeneous_X (R := R) (groupWeight 1 1) ((0 : Fin 1), (0 : Fin 1))
  have hw : groupWeight 1 1 ((0 : Fin 1), (0 : Fin 1)) = fun _ => 1 := by
    funext i
    rw [Fin.fin_one_eq_zero i]
    simp [groupWeight]
  rw [hw] at h
  exact h
end GroundTheory.Heights₂.Heights

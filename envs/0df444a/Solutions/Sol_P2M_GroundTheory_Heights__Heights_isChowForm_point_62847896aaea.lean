-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isChowForm_point_62847896aaea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:46:38.809852+00:00
-- url     : https://prove2.me/submissions/f12eb6d6-915d-455b-b648-84f6789bc297

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_X_dvd_iff_constantCoeff_eq_zero_c0c6267dacb0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_incidence_point_247b5a18c1c3

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
theorem _root_.solution (F : Type*) [Field F] :
    IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) F)) 1 (X (0, 0)) := by
  refine ⟨X_ne_zero _, fun g => ?_⟩
  rw [X_dvd_iff_constantCoeff_eq_zero]
  simp only [mem_incidence_point, forall_eq, aeval_zero]
  exact map_eq_zero_iff _ (algebraMap F (AlgebraicClosure F)).injective
end GroundTheory.Heights₂.Heights

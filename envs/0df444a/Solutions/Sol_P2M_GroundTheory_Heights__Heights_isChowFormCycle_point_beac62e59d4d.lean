-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isChowFormCycle_point_beac62e59d4d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:54:31.302024+00:00
-- url     : https://prove2.me/submissions/d2648df9-6392-43ee-b38b-b84d96ca3823

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isChowForm_point_62847896aaea

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
    IsChowFormCycle (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 1) F)) 1) 1 (X (0, 0)) := by
  refine ⟨1, one_ne_zero, fun _ => X (0, 0), fun W hW => ?_, ?_⟩
  · rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hW
    subst hW
    exact isChowForm_point F
  · rw [Finsupp.support_single _ one_ne_zero]
    simp
end GroundTheory.Heights₂.Heights

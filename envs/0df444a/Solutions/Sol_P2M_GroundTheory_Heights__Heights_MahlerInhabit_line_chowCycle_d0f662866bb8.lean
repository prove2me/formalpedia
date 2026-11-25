-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_chowCycle_d0f662866bb8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:22:22.961572+00:00
-- url     : https://prove2.me/submissions/1c365039-882a-46c7-bab1-1baba03d15ed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_isChowForm_line_d0d771512121


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
open GroundTheory.Heights₂.Heights.MahlerInhabit
namespace GroundTheory.Heights₂.Heights.MahlerInhabit
theorem _root_.solution :
    IsChowFormCycle (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) 2 LineChowForm.D2 := by
  refine ⟨1, one_ne_zero, fun _ => LineChowForm.D2, fun W hW => ?_, ?_⟩
  · rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hW
    subst hW
    exact LineChowForm.isChowForm_line
  · rw [Finsupp.support_single _ one_ne_zero]
    simp
end GroundTheory.Heights₂.Heights.MahlerInhabit

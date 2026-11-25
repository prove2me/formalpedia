-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_data_e3a3d31f3424
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:31:31.958582+00:00
-- url     : https://prove2.me/submissions/1a96d9b0-21d2-4a88-b809-e3f473cf95c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_chowCycle_d0f662866bb8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_isMultiHomog_line_400283483dc9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_isProjPrime_line_6c88d2fbf567


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
    IsChowCycleData (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) 1 1 LineChowForm.D2 := by
  refine ⟨fun W hW => ?_, line_chowCycle, LineChowForm.isMultiHomog_line⟩
  rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hW
  subst hW
  exact LineChowForm.isProjPrime_line
end GroundTheory.Heights₂.Heights.MahlerInhabit

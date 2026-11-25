-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_pair_448a64dfacca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:41:18.686686+00:00
-- url     : https://prove2.me/submissions/4fff1a17-0ca8-454d-8833-f00164f9c425

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_data_e3a3d31f3424
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_linForm_coord_469bf5e55bec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_cycleSection_line_d8b023ba59d2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_proper_a0a8ffcd8fdb

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
    IsChowCycleData (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) 1 1 LineChowForm.D2 ∧
      IsAdmissible (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) (coord 0) ∧
      IsAdmissible (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) (coord 1) ∧
      IsAdmissible (cycleSection (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) (coord 0)) (coord 1) ∧
      IsAdmissible (cycleSection (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) (coord 1)) (coord 0) := by
  have hadm : ∀ a : Fin 2, IsAdmissible (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) (coord a) := by
    intro a W hW
    rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hW
    subst hW
    rw [linForm_coord, Ideal.mem_bot]
    exact X_ne_zero _
  refine ⟨line_data, hadm 0, hadm 1, ?_, ?_⟩
  · rw [cycleSection_line]; exact line_proper 0 1 (by decide)
  · rw [cycleSection_line]; exact line_proper 1 0 (by decide)
end GroundTheory.Heights₂.Heights.MahlerInhabit

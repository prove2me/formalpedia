-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_prime_pair_30334369fc3b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:24:17.281798+00:00
-- url     : https://prove2.me/submissions/8985eab9-b167-4d18-8d1b-0eb7bf45fbff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_linForm_coord_469bf5e55bec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_proper_a0a8ffcd8fdb
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
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧ linForm (coord 0) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      linForm (coord 1) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      IsAdmissible (divCycle (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) (coord 0)) (coord 1) := by
  refine ⟨LineChowForm.isProjPrime_line, ?_, ?_, line_proper 0 1 (by decide)⟩ <;>
  · rw [linForm_coord, Ideal.mem_bot]; exact X_ne_zero _
end GroundTheory.Heights₂.Heights.MahlerInhabit

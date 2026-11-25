-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MahlerInhabit_point_line_5dbce2abefb8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:24:46.803562+00:00
-- url     : https://prove2.me/submissions/13d209b0-ad2e-49cf-8b82-5874a5151466

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler

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
    ∀ x : Fin 1 → ℂ, (∀ q ∈ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)), eval x q = 0) ↔
      ∃ t : ℂ, x = t • (fun _ => (1 : ℂ)) := by
  intro x
  constructor
  · intro _
    exact ⟨x 0, funext fun j => by rw [Fin.fin_one_eq_zero j]; simp⟩
  · rintro - q hq
    rw [Ideal.mem_bot] at hq
    simp [hq]
end GroundTheory.Heights₂.Heights.MahlerInhabit

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointChowForm_hypotheses_inhabited_be7bb473e8ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:13:29.217633+00:00
-- url     : https://prove2.me/submissions/bfb1ddc6-c769-4a5e-92ed-0c576c669876

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_point_line_5dbce2abefb8
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
open MvPolynomial MeasureTheory Matrix
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace PointChowForm
theorem _root_.solution :
    IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1 (X (0, 0)) ∧ (fun _ : Fin 1 => (1 : ℂ)) ≠ 0 ∧
      ∀ x : Fin 1 → ℂ, (∀ q ∈ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)), eval x q = 0) ↔
        ∃ t : ℂ, x = t • (fun _ => (1 : ℂ)) :=
  ⟨isChowForm_point ℂ, fun h0 => one_ne_zero (congrFun h0 0), MahlerInhabit.point_line⟩
end PointChowForm
end GroundTheory.Heights₂.Heights

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IncidenceGeneric_hypotheses_inhabited_d8c47dbf8773
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:33:39.983401+00:00
-- url     : https://prove2.me/submissions/660dd48f-4618-447d-af16-a12c85ae1584

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_genPt_bot_zero_ne_zero_2941ae6aaa72

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
namespace GroundTheory.Heights₂.Heights
namespace IncidenceGeneric
theorem _root_.solution :
    (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)).IsPrime ∧
      ∑ j, (fun _ => (genPt (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) 0)⁻¹) j *
        genPt (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) j = 1 := by
  refine ⟨Ideal.isPrime_bot, ?_⟩
  rw [Fin.sum_univ_one]
  exact inv_mul_cancel₀ genPt_bot_zero_ne_zero
end IncidenceGeneric
end GroundTheory.Heights₂.Heights

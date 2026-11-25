-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ringKrullDim_curveLocalRing_line_968c08547264
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:39:57.167276+00:00
-- url     : https://prove2.me/submissions/9e91a9ae-4598-4cb3-8804-18a22d187a9d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_height_ker_eval_line_99b464f3247b

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
open MvPolynomial ComplexSets
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    ringKrullDim (curveLocalRing (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 0) = 1 := by
  rw [ringKrullDim_eq_of_ringEquiv curveLocalRingLineEquiv,
    IsLocalization.AtPrime.ringKrullDim_eq_height (RingHom.ker (eval (0 : Fin 1 → ℂ))),
    height_ker_eval_line]
  rfl
end GroundTheory.Heights₂.Heights

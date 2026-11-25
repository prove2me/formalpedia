-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_eval_shiftPoly_461cf4c54608
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:53:10.534322+00:00
-- url     : https://prove2.me/submissions/706f1805-9769-4e14-9472-3daa679fdd47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMixedDiffConst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.MixedDiffConst
variable {K : Type}
namespace GroundTheory.Heights₂.Heights.FieldNumbers.MixedDiffConst
theorem _root_.solution (b : K → ℤ) (p : MvPolynomial K ℚ) (x : K → ℚ) :
    eval x (shiftPoly b p) = eval (fun k => x k - b k) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [shiftPoly]
  | add p q hp hq => simp only [shiftPoly, map_add] at hp hq ⊢; rw [hp, hq]
  | mul_X p k hp => simp only [shiftPoly, map_mul] at hp ⊢; rw [hp]; simp
end GroundTheory.Heights₂.Heights.FieldNumbers.MixedDiffConst

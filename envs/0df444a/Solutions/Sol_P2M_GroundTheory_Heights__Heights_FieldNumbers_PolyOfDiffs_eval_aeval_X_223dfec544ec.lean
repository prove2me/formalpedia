-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_eval_aeval_X_223dfec544ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:53:03.207804+00:00
-- url     : https://prove2.me/submissions/a92f98fb-d30e-4ed0-aa71-e3ee09032480

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPolyOfDiffs

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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
open GroundTheory.Heights₂.Heights.FieldNumbers.PolyOfDiffs
variable {K : Type}
variable [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PolyOfDiffs
theorem _root_.solution (y : K → ℚ) (k : K) (F : Polynomial ℚ) :
    eval y (Polynomial.aeval (X k) F) = F.eval (y k) := by
  induction F using Polynomial.induction_on with
  | C a => simp
  | add p r hp hr => rw [map_add, map_add, hp, hr, Polynomial.eval_add]
  | monomial n a _ => simp
end GroundTheory.Heights₂.Heights.FieldNumbers.PolyOfDiffs

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_foldr_diffStep_shift_c1d731c42587
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:53:21.839967+00:00
-- url     : https://prove2.me/submissions/bdda6b54-42f4-43c4-868f-4c4fee4ca434

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMultEqualsCoeff

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
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.MultEqualsCoeff
variable {K : Type*}
namespace GroundTheory.Heights₂.Heights.FieldNumbers.MultEqualsCoeff
theorem _root_.solution (h : (K → ℤ) → ℤ) (c : K → ℤ) :
    ∀ L : List (K → ℤ),
      L.foldr diffStep (fun m => h (m - c)) = fun m => L.foldr diffStep h (m - c)
  | [] => rfl
  | b :: L => by
      simp only [List.foldr_cons]
      rw [solution h c L]
      funext m
      simp only [diffStep, sub_right_comm m b c]
end GroundTheory.Heights₂.Heights.FieldNumbers.MultEqualsCoeff

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_foldr_diffStep_zero_cfe94599070f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:53:27.03356+00:00
-- url     : https://prove2.me/submissions/2d11119a-f7e5-48d9-a1ac-1e0b361acb2e

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
theorem _root_.solution : ∀ L : List (K → ℤ), L.foldr diffStep (0 : (K → ℤ) → ℤ) = 0
  | [] => rfl
  | b :: L => by
      simp only [List.foldr_cons, solution L]
      funext m
      simp [diffStep]
end GroundTheory.Heights₂.Heights.FieldNumbers.MultEqualsCoeff

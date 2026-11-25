-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_foldr_diffStep_sum_77af3311680b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:53:23.972026+00:00
-- url     : https://prove2.me/submissions/52ee7ddd-ebfb-482f-abce-159071049871

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
theorem _root_.solution {J : Type*} (s : Finset J) (f : J → (K → ℤ) → ℤ) :
    ∀ L : List (K → ℤ), L.foldr diffStep (∑ j ∈ s, f j) = ∑ j ∈ s, L.foldr diffStep (f j)
  | [] => rfl
  | b :: L => by
      simp only [List.foldr_cons]
      rw [solution s f L]
      funext m
      simp only [diffStep, Finset.sum_apply, Finset.sum_sub_distrib]
end GroundTheory.Heights₂.Heights.FieldNumbers.MultEqualsCoeff

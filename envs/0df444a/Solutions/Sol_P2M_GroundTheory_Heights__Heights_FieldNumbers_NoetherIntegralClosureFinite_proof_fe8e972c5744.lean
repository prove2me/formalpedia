-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_NoetherIntegralClosureFinite_proof_fe8e972c5744
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:55:43.541853+00:00
-- url     : https://prove2.me/submissions/356d4024-40f4-4883-94ef-a68bb237f92d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsNoetherIntegralClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_NoetherReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_NoetherCharP
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PNoetherIntegralClosure
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_integralClosure_mvPolynomial_of_charP_2951564eb6bc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_integralClosure_mvPolynomial_of_charZero_f3c1cd062f3c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_integralClosure_of_forall_mvPolynomial_4e8918a7d574


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
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace NoetherIntegralClosureFinite
theorem _root_.solution : NoetherIntegralClosureFinite.Statement := by
  intro k A _ _ _ _ _ K _ _ _ L _ _ _ _ _
  refine finite_integralClosure_of_forall_mvPolynomial k A K L fun s L' _ _ _ _ _ => ?_
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hp' | rfl
  · have : Fact p.Prime := ⟨hp'⟩
    exact finite_integralClosure_mvPolynomial_of_charP k p s L'
  · have : CharZero k := CharP.charP_to_charZero k
    exact finite_integralClosure_mvPolynomial_of_charZero k s L'
end NoetherIntegralClosureFinite
end GroundTheory.Heights₂.Heights.FieldNumbers

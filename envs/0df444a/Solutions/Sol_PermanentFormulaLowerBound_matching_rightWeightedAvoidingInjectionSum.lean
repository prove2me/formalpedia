-- Prove2me | solution 1 for PermanentFormulaLowerBound.matching_rightWeightedAvoidingInjectionSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/711c77e3-28d9-47bc-a652-2ab9625fdc96

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_sum_sumEmbedding_right_weight
import Theorems.Thm_PermanentFormulaLowerBound_matching_card_omitted_external

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {F : Type*} [CommSemiring F] {ell m : ℕ}
    (q : Fin m → F) (P Q : Finset (Fin ell)) (a : Fin m) :
    (∑ rho : (↥P ⊕ ↥Q ↪ {j : Fin m // j ≠ a}),
      ∏ v : ↥Q,
        q (rho (Sum.inr v)).1 ^ (2 ^ (v.1 : ℕ))) =
      ((m - 1 - Q.card).descFactorial P.card : F) *
        matchingAvoidingInjectionSum q Q a := by
  classical
  let w : (↥Q ↪ {j : Fin m // j ≠ a}) → F :=
    fun rho => ∏ v : ↥Q, q (rho v).1 ^ (2 ^ (v.1 : ℕ))
  have h := sum_sumEmbedding_right_weight
    (α := ↥P) (γ := {j : Fin m // j ≠ a}) w
  simpa [w, matchingAvoidingInjectionSum,
    matching_card_omitted_external] using h
end PermanentFormulaLowerBound

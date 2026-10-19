-- Prove2me | solution 1 for PermanentFormulaLowerBound.matching_leftWeightedAvoidingInjectionSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/2c08fd9e-f130-4dd9-a79d-1a322cd20084

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_sum_sumEmbedding_left_weight
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
    (p : Fin m → F) (P Q : Finset (Fin ell)) (b : Fin m) :
    (∑ rho : (↥P ⊕ ↥Q ↪ {j : Fin m // j ≠ b}),
      ∏ u : ↥P,
        p (rho (Sum.inl u)).1 ^ (2 ^ (u.1 : ℕ))) =
      ((m - 1 - P.card).descFactorial Q.card : F) *
        matchingAvoidingInjectionSum p P b := by
  classical
  let w : (↥P ↪ {j : Fin m // j ≠ b}) → F :=
    fun rho => ∏ u : ↥P, p (rho u).1 ^ (2 ^ (u.1 : ℕ))
  have h := sum_sumEmbedding_left_weight
    (β := ↥Q) (γ := {j : Fin m // j ≠ b}) w
  simpa [w, matchingAvoidingInjectionSum,
    matching_card_omitted_external] using h
end PermanentFormulaLowerBound

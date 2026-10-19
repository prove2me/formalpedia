-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingMarkedPermanent_split_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/442cac37-5179-4cdc-a5f6-6826542851d9

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_permanentPolynomial_eq_sum
import Theorems.Thm_PermanentFormulaLowerBound_matchingPermutation_split_monomial

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {n : ℕ} {Y : Type u} (d : Y ↪ Fin n × Fin n) :
    MvPolynomial.sumAlgEquiv ℂ Y (matchingOutside d)
        (matchingMarkedPermanent d) =
      ∑ σ : Equiv.Perm (Fin n),
        MvPolynomial.monomial (matchingPermutationExponent d σ)
          (matchingPermutationOutsideProduct d σ) := by
  classical
  unfold matchingMarkedPermanent
  rw [permanentPolynomial_eq_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  exact matchingPermutation_split_monomial d σ
end PermanentFormulaLowerBound

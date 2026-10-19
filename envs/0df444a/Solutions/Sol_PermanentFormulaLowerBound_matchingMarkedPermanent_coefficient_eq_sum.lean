-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingMarkedPermanent_coefficient_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/2fa44748-c654-4919-a7a6-58cab6dd3e10

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingMarkedPermanent_split_eq_sum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {n : ℕ} {Y : Type u} [DecidableEq Y]
    (d : Y ↪ Fin n × Fin n)
    (α : Y →₀ ℕ) :
    coefficientPolynomial (matchingMarkedPermanent d) α =
      ∑ σ : Equiv.Perm (Fin n),
        if matchingPermutationExponent d σ = α then
          matchingPermutationOutsideProduct d σ
        else 0 := by
  classical
  unfold coefficientPolynomial
  rw [matchingMarkedPermanent_split_eq_sum,
    MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp [MvPolynomial.coeff_monomial]
end PermanentFormulaLowerBound

-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingMarkedPermanent_evaluated_coefficient_pderiv_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/3b5b2795-f58f-4dc4-83eb-2601ecfbfa46

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingMarkedPermanent_coefficient_pderiv_eq_sum

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
    (α : Y →₀ ℕ) (z : matchingOutside d)
    (ξ : matchingOutside d → ℂ) :
    MvPolynomial.eval ξ
        (MvPolynomial.pderiv z
          (coefficientPolynomial (matchingMarkedPermanent d) α)) =
      ∑ σ : Equiv.Perm (Fin n),
        if matchingPermutationExponent d σ = α then
          MvPolynomial.eval ξ
            (MvPolynomial.pderiv z
              (matchingPermutationOutsideProduct d σ))
        else 0 := by
  classical
  rw [matchingMarkedPermanent_coefficient_pderiv_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp
end PermanentFormulaLowerBound

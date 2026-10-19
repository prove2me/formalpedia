-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingMarkedPermanent_evaluated_coefficient_pderiv_eq_row_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/7306f87e-f8ba-4f64-9a2e-6e0bb4e84f38

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingMarkedPermanent_evaluated_coefficient_pderiv_eq_sum
import Theorems.Thm_PermanentFormulaLowerBound_matchingPermutationOutsideProduct_pderiv

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {n : ℕ} {Y : Type u} [DecidableEq Y]
    (d : Y ↪ Fin n × Fin n) (α : Y →₀ ℕ)
    (z : matchingOutside d) (ξ : matchingOutside d → ℂ) :
    MvPolynomial.eval ξ
        (MvPolynomial.pderiv z
          (coefficientPolynomial (matchingMarkedPermanent d) α)) =
      ∑ σ : Equiv.Perm (Fin n),
        if matchingPermutationExponent d σ = α ∧
          σ z.1.1 = z.1.2 then
          ∏ i : {i : Fin n // i ≠ z.1.1},
            MvPolynomial.eval ξ
              (matchingPermutationOutsideFactor d σ i.1)
        else 0 := by
  classical
  rw [matchingMarkedPermanent_evaluated_coefficient_pderiv_eq_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [matchingPermutationOutsideProduct_pderiv]
  split_ifs <;> simp_all
end PermanentFormulaLowerBound

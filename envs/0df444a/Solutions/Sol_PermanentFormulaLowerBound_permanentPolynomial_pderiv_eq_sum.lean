-- Prove2me | solution 1 for PermanentFormulaLowerBound.permanentPolynomial_pderiv_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/36f4c4ca-81c2-4e65-bd28-d4e847005f77

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_permanentPolynomial_eq_sum
import Theorems.Thm_PermanentFormulaLowerBound_permanentPermutationMonomial_pderiv

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {n : ℕ} (a b : Fin n) :
    MvPolynomial.pderiv (a, b) (permanentPolynomial n) =
      ∑ σ : Equiv.Perm (Fin n),
        if σ a = b then
          ∏ i : {i : Fin n // i ≠ a},
            (MvPolynomial.X (i.1, σ i.1) :
              MvPolynomial (Fin n × Fin n) ℂ)
        else 0 := by
  classical
  rw [permanentPolynomial_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  exact permanentPermutationMonomial_pderiv σ a b
end PermanentFormulaLowerBound

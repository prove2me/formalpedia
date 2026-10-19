-- Prove2me | solution 1 for PermanentFormulaLowerBound.eval_one_permanentPolynomial_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/d1df291a-8001-4f4f-9d13-a6db968da27b

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_permanentPolynomial_pderiv_eq_sum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {n : ℕ} (a b : Fin n) :
    MvPolynomial.eval
        (fun _ : Fin n × Fin n => (1 : ℂ))
        (MvPolynomial.pderiv (a, b) (permanentPolynomial n)) =
      (Fintype.card {σ : Equiv.Perm (Fin n) // σ a = b} : ℂ) := by
  classical
  calc
    MvPolynomial.eval
        (fun _ : Fin n × Fin n => (1 : ℂ))
        (MvPolynomial.pderiv (a, b) (permanentPolynomial n)) =
      ∑ σ : Equiv.Perm (Fin n),
        if σ a = b then (1 : ℂ) else 0 := by
          rw [permanentPolynomial_pderiv_eq_sum, map_sum]
          apply Finset.sum_congr rfl
          intro σ _
          split_ifs <;> simp
    _ = ((Finset.univ.filter
          (fun σ : Equiv.Perm (Fin n) => σ a = b)).card : ℂ) :=
      Finset.sum_boole (fun σ : Equiv.Perm (Fin n) => σ a = b)
        Finset.univ
    _ = (Fintype.card {σ : Equiv.Perm (Fin n) // σ a = b} : ℂ) := by
      rw [Fintype.card_subtype]
end PermanentFormulaLowerBound

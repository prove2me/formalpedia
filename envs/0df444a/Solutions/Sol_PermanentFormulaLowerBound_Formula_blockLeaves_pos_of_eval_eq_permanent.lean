-- Prove2me | solution 1 for PermanentFormulaLowerBound.Formula.blockLeaves_pos_of_eval_eq_permanent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/6c633548-60ca-4f8d-8e7d-679cd4068a57

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_permanentPolynomial_pderiv_ne_zero
import Theorems.Thm_PermanentFormulaLowerBound_Formula_pderiv_eval_eq_zero_of_blockLeaves_eq_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.Formula
namespace PermanentFormulaLowerBound.Formula
theorem _root_.solution
    {n : ℕ} (f : Formula (Fin n × Fin n) ℂ)
    (hf : eval f = permanentPolynomial n)
    (s : Finset (Fin n × Fin n)) (a b : Fin n)
    (hab : (a, b) ∈ s) :
    0 < blockLeaves s f := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have hderiv := pderiv_eval_eq_zero_of_blockLeaves_eq_zero
    f s (a, b) hab hzero
  rw [hf] at hderiv
  exact permanentPolynomial_pderiv_ne_zero a b hderiv
end PermanentFormulaLowerBound.Formula

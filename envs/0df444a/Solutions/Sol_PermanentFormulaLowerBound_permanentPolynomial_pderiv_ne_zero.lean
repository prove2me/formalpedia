-- Prove2me | solution 1 for PermanentFormulaLowerBound.permanentPolynomial_pderiv_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/f52ff7d8-0849-4e45-b5eb-891db32aaf1b

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_eval_one_permanentPolynomial_pderiv

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {n : ℕ} (a b : Fin n) :
    MvPolynomial.pderiv (a, b) (permanentPolynomial n) ≠ 0 := by
  classical
  have hnonempty :
      Nonempty {σ : Equiv.Perm (Fin n) // σ a = b} :=
    ⟨⟨Equiv.swap a b, by simp⟩⟩
  letI : Nonempty {σ : Equiv.Perm (Fin n) // σ a = b} := hnonempty
  intro hzero
  have hcardzero :
      (Fintype.card {σ : Equiv.Perm (Fin n) // σ a = b} : ℂ) = 0 := by
    rw [← eval_one_permanentPolynomial_pderiv a b, hzero]
    simp
  exact (Nat.cast_ne_zero.mpr
    (Fintype.card_ne_zero :
      Fintype.card {σ : Equiv.Perm (Fin n) // σ a = b} ≠ 0)) hcardzero
end PermanentFormulaLowerBound

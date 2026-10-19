-- Prove2me | solution 1 for PermanentRollout.sourceFreeAffineFormFiniteLinearCombination_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/4622eba1-2071-4b81-ac65-aa1d9337d589

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {ι α : Type*} [Fintype α]
    (coefficient : α → ℂ) (form : α → FreeAffineForm ι)
    (values : Array (MvPolynomial ι ℂ)) :
    (sourceFreeAffineFormFiniteLinearCombination coefficient form).eval values =
      ∑ j, MvPolynomial.C (coefficient j) * (form j).eval values := by
  simp only [FreeAffineForm.eval,
    sourceFreeAffineFormFiniteLinearCombination,
    map_sum, map_mul, map_smul]
  simp only [MvPolynomial.smul_eq_C_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring
end PermanentRollout

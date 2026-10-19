-- Prove2me | solution 1 for PermanentRollout.freeAffineExtendedForm_totalDegree_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/5f5c74c7-08d8-43ef-ae05-7e74a20285a0

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_freeAffineGateReference_totalDegree_le_one

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {k n : ℕ} (form : FreeAffineForm (Fin k)) :
    (freeAffineExtendedForm (n := n) form).totalDegree ≤ 1 := by
  classical
  unfold freeAffineExtendedForm
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · simp
    · simp only [Finsupp.linearCombination_apply, Finsupp.sum]
      apply MvPolynomial.totalDegree_finsetSum_le
      intro i hi
      rw [MvPolynomial.smul_eq_C_mul]
      exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  · simp only [Finsupp.linearCombination_apply, Finsupp.sum]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro i hi
    rw [MvPolynomial.smul_eq_C_mul]
    exact (MvPolynomial.totalDegree_mul _ _).trans
      (by simpa using
        freeAffineGateReference_totalDegree_le_one (k := k) (n := n) i)
end PermanentRollout

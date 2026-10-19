-- Prove2me | solution 1 for PermanentRollout.freeAffineInstructionRhs_mem_gate_vars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/e56362ec-9522-4760-8edf-8becaec7dd81

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_freeAffineGateReference_mem_vars
import Theorems.Thm_PermanentRollout_freeAffineExtendedForm_mem_gate_vars

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {k n : ℕ} (instruction : FreeAffineInstruction (Fin k))
    (position : Fin n)
    (hvalid : instruction.referencesBounded position.val)
    (i : Fin n)
    (hi : Sum.inr i ∈
      (freeAffineInstructionRhs (n := n) instruction).vars) :
    i.val < position.val := by
  classical
  cases instruction with
  | affine form =>
      simp only [FreeAffineInstruction.referencesBounded,
        decide_eq_true_eq] at hvalid
      exact freeAffineExtendedForm_mem_gate_vars
        form position.val hvalid i hi
  | mul left right =>
      simp only [FreeAffineInstruction.referencesBounded,
        Bool.and_eq_true, decide_eq_true_eq] at hvalid
      change Sum.inr i ∈
        (freeAffineGateReference (k := k) (n := n) left *
          freeAffineGateReference (k := k) (n := n) right).vars at hi
      have hmul := MvPolynomial.vars_mul
        (freeAffineGateReference (k := k) (n := n) left)
        (freeAffineGateReference (k := k) (n := n) right) hi
      rw [Finset.mem_union] at hmul
      rcases hmul with hl | hr
      · rw [freeAffineGateReference_mem_vars left i hl]
        exact hvalid.1
      · rw [freeAffineGateReference_mem_vars right i hr]
        exact hvalid.2
end PermanentRollout

-- Prove2me | solution 1 for PermanentRollout.freeAffineInstruction_program_cost_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/e6db8576-ea80-406c-8f0c-9976880a63fa

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {k : ℕ} (program : List (FreeAffineInstruction (Fin k))) :
    (program.map fun instruction =>
      if instruction.isMultiplication then (2 : ℕ) else 1).prod =
      2 ^ (program.filter FreeAffineInstruction.isMultiplication).length := by
  induction program with
  | nil => simp
  | cons instruction rest ih =>
      cases instruction with
      | affine form =>
          change
            1 * (rest.map fun instruction =>
              if instruction.isMultiplication then (2 : ℕ) else 1).prod =
              2 ^ (rest.filter FreeAffineInstruction.isMultiplication).length
          simpa only [one_mul] using ih
      | mul left right =>
          change
            2 * (rest.map fun instruction =>
              if instruction.isMultiplication then (2 : ℕ) else 1).prod =
              2 ^ ((rest.filter FreeAffineInstruction.isMultiplication).length + 1)
          calc
            2 * (rest.map fun instruction =>
              if instruction.isMultiplication then (2 : ℕ) else 1).prod =
                2 * 2 ^ (rest.filter FreeAffineInstruction.isMultiplication).length :=
                  congrArg (fun z : ℕ => 2 * z) ih
            _ = 2 ^ ((rest.filter FreeAffineInstruction.isMultiplication).length + 1) := by
                  rw [pow_succ, Nat.mul_comm]
end PermanentRollout

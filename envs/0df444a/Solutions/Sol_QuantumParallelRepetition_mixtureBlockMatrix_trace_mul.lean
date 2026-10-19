-- Prove2me | solution 1 for QuantumParallelRepetition.mixtureBlockMatrix_trace_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/c737793e-e4f2-4a58-ae02-73a4d95bea43

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
variable {X Y A B : Type*} {J : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype J] [DecidableEq J]
variable {G : Game X Y A B}
namespace QuantumParallelRepetition
theorem _root_.solution
    (p : J → ℝ) (S : J → Strategy G)
    (E : ∀ j : J,
      Matrix ((S j).Alice × (S j).Bob)
        ((S j).Alice × (S j).Bob) ℂ) :
    Matrix.trace (mixtureBlockMatrix p S * Matrix.blockDiagonal' E) =
      ∑ j : J, p j • Matrix.trace ((S j).state.matrix * E j) := by
  unfold mixtureBlockMatrix
  rw [← Matrix.blockDiagonal'_mul, Matrix.trace_blockDiagonal']
  simp [Matrix.trace_smul]
end QuantumParallelRepetition

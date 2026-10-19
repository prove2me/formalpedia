-- Prove2me | solution 1 for QuantumParallelRepetition.flaggedQuestionWeight_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/d5b13c80-2a81-417b-92a8-79a3f56290b2

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
variable {X Y A B dA dB J : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
variable [Fintype J] [DecidableEq J]
omit [DecidableEq J]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) (flagWeight : J → ℝ)
    (normalized : (∑ j, flagWeight j) = 1) :
    (∑ ω : J × (X × Y),
      flaggedQuestionWeight G flagWeight ω) = 1 := by
  classical
  simp [flaggedQuestionWeight, Fintype.sum_prod_type,
    ← Finset.mul_sum, G.weight_normalized, normalized]
end QuantumParallelRepetition

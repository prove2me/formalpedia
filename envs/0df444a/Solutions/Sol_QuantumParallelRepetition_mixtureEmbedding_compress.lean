-- Prove2me | solution 1 for QuantumParallelRepetition.mixtureEmbedding_compress
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/b2135530-81e9-47ec-922f-02ecf9b4ad85

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
theorem _root_.solution (S : J → Strategy G)
    (E : Matrix (mixtureAlice S × mixtureBob S)
      (mixtureAlice S × mixtureBob S) ℂ) :
    (mixtureEmbedding S)ᴴ * E * mixtureEmbedding S =
      E.submatrix (mixtureMatchedIndex S) (mixtureMatchedIndex S) := by
  classical
  ext i j
  simp [mixtureEmbedding, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.submatrix_apply]
end QuantumParallelRepetition

-- Prove2me | solution 1 for QuantumParallelRepetition.mixtureJointEffect_compress
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/52b8e60c-cb00-4c11-91b4-1b7482737cdc

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
    (x : X) (y : Y) (a : A) (b : B) :
    (((mixtureAlicePOVM S x).effect a ⊗ₖ
      (mixtureBobPOVM S y).effect b).submatrix
        (mixtureMatchedIndex S) (mixtureMatchedIndex S)) =
      Matrix.blockDiagonal' fun j =>
        (S j).jointEffect x y a b := by
  classical
  ext ⟨i, u, v⟩ ⟨j, u', v'⟩
  by_cases h : i = j
  · subst j
    simp [Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
      mixtureMatchedIndex, mixtureAlicePOVM, mixtureBobPOVM,
      Matrix.blockDiagonal'_apply, Strategy.jointEffect]
  · simp [Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
      mixtureMatchedIndex, mixtureAlicePOVM, mixtureBobPOVM,
      Matrix.blockDiagonal'_apply, Strategy.jointEffect, h]
end QuantumParallelRepetition

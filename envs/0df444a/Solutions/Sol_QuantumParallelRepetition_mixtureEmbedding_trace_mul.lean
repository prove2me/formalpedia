-- Prove2me | solution 1 for QuantumParallelRepetition.mixtureEmbedding_trace_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/388f0155-03e4-4165-a6e1-3b1baad112c1

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_mixtureEmbedding_compress

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
    (R : Matrix (mixtureMatched S) (mixtureMatched S) ℂ)
    (E : Matrix (mixtureAlice S × mixtureBob S)
      (mixtureAlice S × mixtureBob S) ℂ) :
    Matrix.trace
      ((mixtureEmbedding S * R * (mixtureEmbedding S)ᴴ) * E) =
      Matrix.trace
        (R * E.submatrix (mixtureMatchedIndex S)
          (mixtureMatchedIndex S)) := by
  calc
    Matrix.trace
        ((mixtureEmbedding S * R * (mixtureEmbedding S)ᴴ) * E) =
        Matrix.trace
          ((mixtureEmbedding S * R) * ((mixtureEmbedding S)ᴴ * E)) := by
            congr 1
            simp [Matrix.mul_assoc]
    _ = Matrix.trace
          (((mixtureEmbedding S)ᴴ * E) * (mixtureEmbedding S * R)) :=
          Matrix.trace_mul_comm _ _
    _ = Matrix.trace
          (((mixtureEmbedding S)ᴴ * E * mixtureEmbedding S) * R) := by
            congr 1
            simp [Matrix.mul_assoc]
    _ = Matrix.trace
          (R * ((mixtureEmbedding S)ᴴ * E * mixtureEmbedding S)) :=
          Matrix.trace_mul_comm _ _
    _ = Matrix.trace
          (R * E.submatrix (mixtureMatchedIndex S)
            (mixtureMatchedIndex S)) := by
          rw [mixtureEmbedding_compress]
end QuantumParallelRepetition

-- Prove2me | solution 1 for QuantumParallelRepetition.finiteLocalPurificationVector_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/46ba128e-bc2a-486a-9416-a055010e3650

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_rectangular_matrix_quadratic_compression
import Theorems.Thm_QuantumParallelRepetition_finiteLocalPurificationJointMatrix_compression

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
namespace QuantumParallelRepetition
theorem _root_.solution
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype eA] [Fintype eB]
    [DecidableEq eA] [DecidableEq eB]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ) (KB : Matrix eB S.Bob ℂ)
    (EA : Matrix eA eA ℂ) (EB : Matrix eB eB ℂ) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (eA × (S.Alice × S.Bob)) × eB) (𝕜 := ℂ)
        (((EA ⊗ₖ
          (1 : Matrix (S.Alice × S.Bob)
            (S.Alice × S.Bob) ℂ)) ⊗ₖ EB)))
      (finiteLocalPurificationVector S KA KB) =
      bornTracePairing S.state.matrix
        (KA.conjTranspose * EA * KA)
        (KB.conjTranspose * EB * KB) := by
  unfold finiteLocalPurificationVector
  rw [rectangular_matrix_quadratic_compression,
    finiteLocalPurificationJointMatrix_compression]
  exact strategyPurificationVector_quadratic S
    (KA.conjTranspose * EA * KA)
    (KB.conjTranspose * EB * KB)
end QuantumParallelRepetition

-- Prove2me | solution 1 for QuantumParallelRepetition.matrixQuadraticExpectation_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/edd7080f-e048-4e71-8549-265d5f826c41

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_matrixQuadraticExpectation_expand
import Theorems.Thm_QuantumParallelRepetition_finiteSum_injective_support

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (f : d → e) (injective : Function.Injective f)
    (M : Matrix e e ℂ) (N : Matrix d d ℂ)
    (v : EuclideanSpace ℂ e) (z : EuclideanSpace ℂ d)
    (included : ∀ i : d, v (f i) = z i)
    (supported : ∀ j : e, (∀ i : d, f i ≠ j) → v j = 0)
    (compressed : ∀ i j : d, M (f i) (f j) = N i j) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := e) (𝕜 := ℂ) M) v =
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) N) z := by
  classical
  rw [matrixQuadraticExpectation_expand,
    matrixQuadraticExpectation_expand]
  congr 1
  rw [finiteSum_injective_support f injective
    (fun i : e => (∑ j : e, M i j * v j) * star (v i))
    (by
      intro i outside
      simp [supported i outside])]
  apply Finset.sum_congr rfl
  intro i _
  rw [included i]
  congr 1
  rw [finiteSum_injective_support f injective
    (fun j : e => M (f i) j * v j)
    (by
      intro j outside
      simp [supported j outside])]
  apply Finset.sum_congr rfl
  intro j _
  rw [compressed i j, included j]
end QuantumParallelRepetition

-- Prove2me | solution 1 for QuantumParallelRepetition.actualStoppingQuestionLocalWinningEffect_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/a425276d-b171-423f-8a48-257c4f6ff0ad

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_rectangular_matrix_quadratic_compression
import Theorems.Thm_QuantumParallelRepetition_sourceHistoryQuadraticExpectation_matrix_sum
import Theorems.Thm_QuantumParallelRepetition_unitaryConjugatePOVM_jointEffect

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] Classical.propDecidable
variable {X Y A B R : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype R] [DecidableEq R]
variable {ι : R → Type}
variable [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (r : R) → Y → POVM B (ι r))
    (U : X → Matrix.unitaryGroup (Σ r, ι r) ℂ)
    (V : Y → Matrix.unitaryGroup (Σ r, ι r) ℂ)
    (z : EuclideanSpace ℂ ((Σ r, ι r) × (Σ r, ι r)))
    (normalized : ‖z‖ = 1)
    (x : X) (y : Y) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (Σ r, ι r) × (Σ r, ι r)) (𝕜 := ℂ)
        (pureVerifierEffect G z normalized
          (fun x => unitaryConjugatePOVM (U x)
            (dependentBlockPOVM (fun r => PA r x)))
          (fun y => unitaryConjugatePOVM (V y)
            (dependentBlockPOVM (fun r => PB r y)))
          x y)) z =
      quadraticExpectation
        (Matrix.toEuclideanCLM
          (n := (Σ r, ι r) × (Σ r, ι r)) (𝕜 := ℂ)
          (actualStoppingGlobalWinningEffect
            G PA PB x y))
        (actualStoppingQuestionLocalAction
          (U x) (V y) z) := by
  classical
  change
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (Σ r, ι r) × (Σ r, ι r)) (𝕜 := ℂ)
        (∑ a : A, ∑ b : B,
          if G.predicate x y a b = true then
            (unitaryConjugatePOVM (U x)
              (dependentBlockPOVM
                (fun r => PA r x))).effect a ⊗ₖ
            (unitaryConjugatePOVM (V y)
              (dependentBlockPOVM
                (fun r => PB r y))).effect b
          else 0)) z =
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (Σ r, ι r) × (Σ r, ι r)) (𝕜 := ℂ)
        (∑ a : A, ∑ b : B,
          if G.predicate x y a b = true then
            (dependentBlockPOVM
              (fun r => PA r x)).effect a ⊗ₖ
            (dependentBlockPOVM
              (fun r => PB r y)).effect b
          else 0))
      (actualStoppingQuestionLocalAction
        (U x) (V y) z)
  rw [sourceHistoryQuadraticExpectation_matrix_sum,
    sourceHistoryQuadraticExpectation_matrix_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [sourceHistoryQuadraticExpectation_matrix_sum,
    sourceHistoryQuadraticExpectation_matrix_sum]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs with accepted
  · rw [unitaryConjugatePOVM_jointEffect]
    exact (rectangular_matrix_quadratic_compression
      (((U x : Matrix (Σ r, ι r) (Σ r, ι r) ℂ) ⊗ₖ
        (V y : Matrix (Σ r, ι r) (Σ r, ι r) ℂ)))
      (((dependentBlockPOVM (fun r => PA r x)).effect a) ⊗ₖ
       ((dependentBlockPOVM (fun r => PB r y)).effect b))
      z).symm
  · simp [quadraticExpectation]
end QuantumParallelRepetition

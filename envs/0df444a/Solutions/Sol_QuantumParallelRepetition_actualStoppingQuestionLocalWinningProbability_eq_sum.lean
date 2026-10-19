-- Prove2me | solution 1 for QuantumParallelRepetition.actualStoppingQuestionLocalWinningProbability_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/ca235a01-73ab-407c-807e-407768fa7e6b

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_pureVectorWinningProbability_eq
import Theorems.Thm_QuantumParallelRepetition_actualStoppingGlobalBorn_eq_sum
import Theorems.Thm_QuantumParallelRepetition_actualStoppingQuestionLocalWinningEffect_quadratic

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
    (normalized : ‖z‖ = 1) :
    (pureVectorStrategy G z normalized
      (fun x => unitaryConjugatePOVM (U x)
        (dependentBlockPOVM (fun r => PA r x)))
      (fun y => unitaryConjugatePOVM (V y)
        (dependentBlockPOVM (fun r => PB r y)))).winProbability =
      ∑ x : X, ∑ y : Y, G.questionWeight x y *
        ∑ r : R, ∑ s : R,
          quadraticExpectation
            (Matrix.toEuclideanCLM (n := ι r × ι s) (𝕜 := ℂ)
              (actualStoppingBranchWinningEffect
                G PA PB r s x y))
            (actualStoppingBranchVector
              (actualStoppingQuestionLocalAction
                (U x) (V y) z) r s) := by
  classical
  rw [pureVectorWinningProbability_eq]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  rw [actualStoppingQuestionLocalWinningEffect_quadratic]
  exact actualStoppingGlobalBorn_eq_sum
    G PA PB (actualStoppingQuestionLocalAction
      (U x) (V y) z) x y
end QuantumParallelRepetition

-- Prove2me | solution 1 for QuantumParallelRepetition.actualStoppingQuestionLocalFlaggedWinningProbability_ge_matched
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/c4a45ae3-4194-4586-8c17-632b6ef7632c

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_pureFlaggedStrategy_winProbability
import Theorems.Thm_QuantumParallelRepetition_actualStoppingQuestionLocalWinningProbability_ge_matched

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
    {L : ℕ} {J : Type} [Fintype J] [DecidableEq J]
    {ι : Fin (L + 1) → Type}
    [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
    (G : Game X Y A B)
    (weight : J → ℝ)
    (weight_nonnegative : ∀ j, 0 ≤ weight j)
    (weight_normalized : (∑ j : J, weight j) = 1)
    (PA : J → (r : Fin (L + 1)) → X → POVM A (ι r))
    (PB : J → (r : Fin (L + 1)) → Y → POVM B (ι r))
    (U : J → X → Matrix.unitaryGroup
      (Σ r : Fin (L + 1), ι r) ℂ)
    (V : J → Y → Matrix.unitaryGroup
      (Σ r : Fin (L + 1), ι r) ℂ)
    (z : J → EuclideanSpace ℂ
      ((Σ r : Fin (L + 1), ι r) ×
       (Σ r : Fin (L + 1), ι r)))
    (normalized : ∀ j, ‖z j‖ = 1) :
    (∑ q : J, weight q *
      (∑ x : X, ∑ y : Y, G.questionWeight x y *
        ∑ j : Fin L,
          quadraticExpectation
            (Matrix.toEuclideanCLM
              (n := ι j.succ × ι j.succ) (𝕜 := ℂ)
              (actualStoppingBranchWinningEffect
                G (PA q) (PB q) j.succ j.succ x y))
            (actualStoppingBranchVector
              (actualStoppingQuestionLocalAction
                (U q x) (V q y) (z q)) j.succ j.succ))) ≤
      (pureFlaggedStrategy G weight weight_nonnegative
        weight_normalized z normalized
        (fun q x => unitaryConjugatePOVM (U q x)
          (dependentBlockPOVM (fun r => PA q r x)))
        (fun q y => unitaryConjugatePOVM (V q y)
          (dependentBlockPOVM (fun r => PB q r y)))).winProbability := by
  classical
  rw [pureFlaggedStrategy_winProbability]
  apply Finset.sum_le_sum
  intro q _
  apply mul_le_mul_of_nonneg_left _ (weight_nonnegative q)
  exact actualStoppingQuestionLocalWinningProbability_ge_matched
    G (PA q) (PB q) (U q) (V q) (z q) (normalized q)
end QuantumParallelRepetition

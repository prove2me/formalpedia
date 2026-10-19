-- Prove2me | solution 1 for QuantumParallelRepetition.actualStoppingGlobalWinningEffect_cross_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/20da7396-1910-4611-aa9d-7c9f130b56d7

import Mathlib
import Definitions.Def_QuantumParallelRepetition

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
variable {ι κ : R → Type}
variable [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
variable [∀ r, Fintype (κ r)] [∀ r, DecidableEq (κ r)]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (s : R) → Y → POVM B (κ s))
    (r s r' s' : R) (x : X) (y : Y)
    (i : ι r) (j : κ s) (i' : ι r') (j' : κ s')
    (different : r ≠ r' ∨ s ≠ s') :
    actualStoppingGlobalWinningEffect G PA PB x y
        (⟨r, i⟩, ⟨s, j⟩) (⟨r', i'⟩, ⟨s', j'⟩) = 0 := by
  classical
  rcases different with left | right
  · unfold actualStoppingGlobalWinningEffect
    simp only [Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    split_ifs
    · simp [dependentBlockPOVM,
        Matrix.blockDiagonal'_apply, left]
    · rfl
  · unfold actualStoppingGlobalWinningEffect
    simp only [Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    split_ifs
    · simp [dependentBlockPOVM,
        Matrix.blockDiagonal'_apply, right]
    · rfl
end QuantumParallelRepetition

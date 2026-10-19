-- Prove2me | solution 1 for QuantumParallelRepetition.sourceHistoryFlag_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/1384f43e-8fc9-4675-ad98-f031dd1c9098

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
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    {n : ℕ} (D : Finset (Fin n))
    (f : SourceHistoryFlag X Y A B D → ℝ) :
    (∑ r : SourceHistoryFlag X Y A B D, f r) =
      ∑ π : SourceRemainingPermutation D,
      ∑ k : Fin (Finset.univ \ D).card,
      ∑ r : FullCoordinateRevealHistory X Y n D
          (sourceRemainingPermutationPrefix D π k.castSucc)
          (sourceRemainingPermutationCoordinate D π k),
      ∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
        f ⟨π, k, r, α, β⟩ := by
  classical
  calc
    (∑ r : SourceHistoryFlag X Y A B D, f r) =
        ∑ t : SourceHistoryFlagTuple X Y A B D,
          f ((sourceHistoryFlagEquiv (X := X) (Y := Y)
            (A := A) (B := B) D).symm t) :=
      ((sourceHistoryFlagEquiv (X := X) (Y := Y)
        (A := A) (B := B) D).symm.sum_comp f).symm
    _ = _ := by
      simp [Fintype.sum_sigma, Fintype.sum_prod_type,
        sourceHistoryFlagEquiv]
end QuantumParallelRepetition

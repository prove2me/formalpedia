-- Prove2me | solution 1 for QuantumParallelRepetition.sourceRemainingPermutationCoordinate_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/ce9f6151-03bf-4747-8a52-995cd55e2281

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators
namespace QuantumParallelRepetition
theorem _root_.solution
    {T : Type*} [AddCommMonoid T]
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (f : Fin n → T) :
    (∑ k : Fin (Finset.univ \ D).card,
      f (sourceRemainingPermutationCoordinate D π k)) =
      ∑ i : SourceRemainingCoordinate D, f i.val := by
  classical
  exact (sourceRemainingPermutationRank D π).symm.sum_comp
    (fun i : SourceRemainingCoordinate D => f i.val)
end QuantumParallelRepetition

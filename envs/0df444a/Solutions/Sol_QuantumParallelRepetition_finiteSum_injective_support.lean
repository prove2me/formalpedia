-- Prove2me | solution 1 for QuantumParallelRepetition.finiteSum_injective_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/9d274fec-c17e-451d-8dc0-8543c4a8176f

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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    {d e K : Type*} [Fintype d] [Fintype e] [AddCommMonoid K]
    (f : d → e) (injective : Function.Injective f)
    (g : e → K)
    (supported : ∀ j : e, (∀ i : d, f i ≠ j) → g j = 0) :
    (∑ j : e, g j) = ∑ i : d, g (f i) := by
  classical
  calc
    (∑ j : e, g j) = ∑ j ∈ Finset.univ.image f, g j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ outside
      apply supported j
      intro i same
      exact outside
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, same⟩)
    _ = ∑ i : d, g (f i) := by
      rw [Finset.sum_image]
      intro i _ j _ same
      exact injective same
end QuantumParallelRepetition

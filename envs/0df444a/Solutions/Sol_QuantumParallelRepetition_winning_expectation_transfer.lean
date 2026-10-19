-- Prove2me | solution 1 for QuantumParallelRepetition.winning_expectation_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/435bb919-3953-45cb-b045-99aedf3aa6e3

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_expectation_le_add_totalVariation

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
namespace QuantumParallelRepetition
theorem _root_.solution
    {ι : Type*} [Fintype ι]
    (p q win : ι → ℝ)
    (hp : (∑ i, p i) = 1)
    (hq : (∑ i, q i) = 1)
    (hzero : ∀ i, 0 ≤ win i)
    (hone : ∀ i, win i ≤ 1) :
    (∑ i, q i * win i) - finiteTotalVariation p q ≤
      ∑ i, p i * win i := by
  have h := expectation_le_add_totalVariation
    q p win hq hp (1 : ℝ) hzero hone
  rw [← finiteTotalVariation_comm p q] at h
  norm_num at h ⊢
  linarith
end QuantumParallelRepetition

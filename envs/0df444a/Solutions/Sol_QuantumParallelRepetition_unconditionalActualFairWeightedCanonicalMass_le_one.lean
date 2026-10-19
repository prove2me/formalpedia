-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairWeightedCanonicalMass_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/0ad9821c-a6df-42ce-beed-efcf89cd321f

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairCanonicalRow_le_one

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] Classical.propDecidable
namespace QuantumParallelRepetition
theorem _root_.solution
    {I : Type} [Fintype I]
    {S B N d L m : ℕ}
    (weight : I → ℝ)
    (weight_nonnegative : ∀ h, 0 ≤ weight h)
    (weight_normalized : (∑ h : I, weight h) = 1)
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : I → BipartiteUnitVector d)
    (fine : ∀ s,
      (d : ℝ) / (N : ℝ) < 1 / (width s + 1)) :
    (∑ h : I, weight h *
      ∑ j : Fin L,
        ‖integratorActualC485CanonicalVector
          (B := B) (m := m) schedule (ξ h) (ζ h) j
          (width_positive (schedule j)) grid
          (fine (schedule j))‖ ^ 2) ≤ 1 := by
  calc
    _ ≤ ∑ h : I, weight h * 1 := by
      apply Finset.sum_le_sum
      intro h _
      exact mul_le_mul_of_nonneg_left
        (unconditionalActualFairCanonicalRow_le_one
          phases grid dimension harmonic width width_positive
          schedule (ξ h) (ζ h) fine)
        (weight_nonnegative h)
    _ = 1 := by simpa using weight_normalized
end QuantumParallelRepetition

-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairCanonicalRow_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/254bf51f-4e5e-4b81-ae87-89b5a7a2e347

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualC485NormalizedDiagonalWork_mass_sum_le_one
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairCanonicalVector_norm_sq

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
    {S B N d L m : ℕ}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (fine : ∀ s,
      (d : ℝ) / (N : ℝ) < 1 / (width s + 1)) :
    (∑ j : Fin L,
      ‖integratorActualC485CanonicalVector
        (B := B) (m := m) schedule ξ ζ j
        (width_positive (schedule j)) grid
        (fine (schedule j))‖ ^ 2) ≤ 1 := by
  calc
    _ = ∑ j : Fin L,
      ‖integratorActualC485NormalizedDiagonalWork
        (B := B) (N := N) width schedule ξ ζ j‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact unconditionalActualFairCanonicalVector_norm_sq
        phases grid harmonic width schedule ξ ζ j
        (width_positive (schedule j)) (fine (schedule j))
    _ ≤ 1 :=
      unconditionalActualC485NormalizedDiagonalWork_mass_sum_le_one
        (m := m) phases grid dimension harmonic
        width width_positive schedule ξ ζ
end QuantumParallelRepetition

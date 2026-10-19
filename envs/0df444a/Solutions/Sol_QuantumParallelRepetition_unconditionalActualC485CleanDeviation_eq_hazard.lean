-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualC485CleanDeviation_eq_hazard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/9addbb30-2a8e-4651-913b-77eb8b08e1ea

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualC485CleanDeviation_sq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
namespace QuantumParallelRepetition
theorem _root_.solution
    {S B N d L m : ℕ}
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (positive : ∀ s, 0 < width s)
    (phases : 0 < B) (grid : 0 < N) (dimension : 0 < d)
    (fine : ∀ s, (d : ℝ) / (N : ℝ) < 1 / (width s + 1)) :
    (∑ j : Fin L,
      ‖integratorActualC485CleanedVector
            (B := B) (m := m) Q width schedule ξ ζ A C j -
          integratorActualC485CanonicalVector
            (B := B) (m := m) schedule ξ ζ j
            (positive (schedule j)) grid (fine (schedule j))‖ ^ 2) =
      dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
        Q m width schedule ξ ζ A C := by
  classical
  simp_rw [unconditionalActualC485CleanDeviation_sq
    Q width schedule ξ ζ A C _ (positive _) phases grid dimension (fine _)]
  unfold dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
  simp_rw [
    dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector_norm_sq]
end QuantumParallelRepetition

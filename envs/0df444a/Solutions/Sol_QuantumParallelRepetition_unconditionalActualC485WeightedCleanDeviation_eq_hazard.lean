-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualC485WeightedCleanDeviation_eq_hazard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/b66e3a27-1d3a-4ad1-8033-cdd2f565d05a

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualC485CleanDeviation_eq_hazard

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
    {ι : Type*} [Fintype ι]
    {S B N d L m : ℕ}
    (law : ι → ℝ)
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : ι → BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (positive : ∀ s, 0 < width s)
    (phases : 0 < B) (grid : 0 < N) (dimension : 0 < d)
    (fine : ∀ s, (d : ℝ) / (N : ℝ) < 1 / (width s + 1)) :
    (∑ u : ι, law u *
      ∑ j : Fin L,
        ‖integratorActualC485CleanedVector
              (B := B) (m := m)
              Q width schedule (ξ u) (ζ u) A C j -
            integratorActualC485CanonicalVector
              (B := B) (m := m) schedule (ξ u) (ζ u) j
              (positive (schedule j)) grid (fine (schedule j))‖ ^ 2) =
      ∑ u : ι, law u *
        dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
          Q m width schedule (ξ u) (ζ u) A C := by
  classical
  apply Finset.sum_congr rfl
  intro u _
  rw [unconditionalActualC485CleanDeviation_eq_hazard
    Q width schedule (ξ u) (ζ u) A C positive phases grid dimension fine]
end QuantumParallelRepetition

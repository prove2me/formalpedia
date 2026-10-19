-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualC485CleanDeviation_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/0f59b2c4-9633-4ae2-a8dd-2ddd461559b4

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalSelectedCopyMatchedBranch_deviation_sq
import Theorems.Thm_QuantumParallelRepetition_integratorActualCanonicalRetainedPhaseTail_norm
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualC485CanonicalVector_eq_correctedIdeal
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualSelectedBranchLocalAction_norm
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualSelectedBranchLocalAction_sub

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
    (j : Fin L)
    (positive : 0 < width (schedule j))
    (phases : 0 < B) (grid : 0 < N) (dimension : 0 < d)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (width (schedule j) + 1)) :
    ‖integratorActualC485CleanedVector
          (B := B) (m := m) Q width schedule ξ ζ A C j -
        integratorActualC485CanonicalVector
          (B := B) (m := m) schedule ξ ζ j positive grid fine‖ ^ 2 =
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ j.val *
        dSVDensityRationalHeterogeneousCommonStopGaugeStageError
          Q (width (schedule j)) m ξ ζ A C := by
  classical
  rw [unconditionalActualC485CanonicalVector_eq_correctedIdeal
    schedule ξ ζ j positive grid dimension fine]
  unfold integratorActualC485CleanedVector
  rw [unconditionalActualSelectedBranchLocalAction_sub,
    unconditionalActualSelectedBranchLocalAction_norm]
  exact unconditionalSelectedCopyMatchedBranch_deviation_sq
    Q width schedule ξ ζ A C j
    (unconditionalActualCanonicalRetainedPhaseTail
      (S := S) (B := B) (N := N) (d := d) (L := L) j)
    (integratorActualCanonicalRetainedPhaseTail_norm
      phases grid dimension j)
end QuantumParallelRepetition

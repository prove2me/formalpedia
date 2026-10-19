-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalSelectedCopyCleanedMatchedBranch_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/ae972957-23d8-47b1-b1ce-f964484c73be

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalMatchedVerifierTensor_norm_sq
import Theorems.Thm_QuantumParallelRepetition_unconditionalSelectedCopyRetainedWork_norm_sq
import Theorems.Thm_QuantumParallelRepetition_unconditionalSelectedCopyCleanedStage_norm_sq

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
    {S N d L B m : ℕ} {τ : Type*} [Fintype τ]
    (phases : 0 < B) (grid : 0 < N) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (Q : ℕ)
    (A C : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) (rest : EuclideanSpace ℂ τ)
    (rest_unit : ‖rest‖ = 1) :
    ‖unconditionalSelectedCopyCleanedMatchedBranch
        Q width schedule ξ ζ A C j rest‖ ^ 2 =
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ j.val *
        dSVDensityRationalHeterogeneousPhysicalStageSuccess
          N width schedule ξ ζ j.val := by
  unfold unconditionalSelectedCopyCleanedMatchedBranch
  rw [unconditionalMatchedVerifierTensor_norm_sq,
    unconditionalSelectedCopyCleanedStage_norm_sq
      phases grid harmonic (width_positive (schedule j)),
    unconditionalSelectedCopyRetainedWork_norm_sq,
    rest_unit]
  simp [dSVDensityRationalHeterogeneousPhysicalStageSuccess,
    dSVDensityRationalHeterogeneousPhysicalStageOutcome,
    j.isLt, mul_comm]
end QuantumParallelRepetition

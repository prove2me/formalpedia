-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalSelectedCopyMatchedBranch_deviation_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/e4da0f05-89e7-43cb-ac7c-02c38a5b07eb

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalMatchedVerifierTensor_norm_sq
import Theorems.Thm_QuantumParallelRepetition_unconditionalSelectedCopy_tensor_sub
import Theorems.Thm_QuantumParallelRepetition_unconditionalSelectedCopyRetainedWork_norm_sq

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
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) (rest : EuclideanSpace ℂ τ)
    (rest_unit : ‖rest‖ = 1) :
    ‖unconditionalSelectedCopyCleanedMatchedBranch
          Q width schedule ξ ζ A C j rest -
        unconditionalSelectedCopyIdealMatchedBranch
          (B := B) (m := m) width schedule ξ ζ j rest‖ ^ 2 =
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ j.val *
        dSVDensityRationalHeterogeneousCommonStopGaugeStageError
          Q (width (schedule j)) m ξ ζ A C := by
  unfold unconditionalSelectedCopyCleanedMatchedBranch
    unconditionalSelectedCopyIdealMatchedBranch
  rw [unconditionalSelectedCopy_tensor_sub,
    unconditionalMatchedVerifierTensor_norm_sq,
    unconditionalSelectedCopyRetainedWork_norm_sq,
    rest_unit]
  unfold dSVDensityRationalHeterogeneousCommonStopGaugeStageError
    unconditionalSelectedCopyCleanedStage
    unconditionalSelectedCopyIdealStage
  ring
end QuantumParallelRepetition

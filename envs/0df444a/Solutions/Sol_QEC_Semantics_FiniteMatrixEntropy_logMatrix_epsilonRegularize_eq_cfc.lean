-- Prove2me | solution 1 for QEC.Semantics.FiniteMatrixEntropy.logMatrix_epsilonRegularize_eq_cfc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:52:22.520996+00:00
-- url     : https://prove2.me/submissions/db50276f-eb28-44f1-8a10-f2bad9aee32a

import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_epsilonRegularize_eq_cfc
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.log2Matrix_apply
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.logMatrix_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder Kronecker TensorProduct
noncomputable section
open QEC.Semantics.FiniteMatrixEntropy
namespace QEC.Semantics.FiniteMatrixEntropy
theorem _root_.solution
    {n : Type v} [Fintype n] [DecidableEq n]
    (B : Matrix n n Complex) (hB : B.PosSemidef) {epsilon : Real} (hepsilon : 0 < epsilon) :
    logMatrix (epsilonRegularize B epsilon)
        (epsilonRegularize_posDef B hB hepsilon).isHermitian =
      hB.isHermitian.cfc (fun x =>
        Real.log ((x + epsilon) / (1 + epsilon * Fintype.card n))) := by
  let f : Real -> Real := fun x =>
    (1 + epsilon * Fintype.card n)⁻¹ * (x + epsilon)
  have hregularized : epsilonRegularize B epsilon = hB.isHermitian.cfc f :=
    epsilonRegularize_eq_cfc B hB.isHermitian epsilon
  have hregularizedCfc : epsilonRegularize B epsilon = cfc f B := by
    rw [hB.isHermitian.cfc_eq]
    exact hregularized
  have hlogContinuous : ContinuousOn Real.log (f '' spectrum Real B) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxnonneg : 0 <= x := by
      obtain ⟨i, rfl⟩ := hB.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hx
      exact hB.eigenvalues_nonneg i
    have hdenom : 0 < 1 + epsilon * Fintype.card n := by positivity
    have hfx : 0 < f x := by
      dsimp [f]
      exact mul_pos (inv_pos.mpr hdenom) (add_pos_of_nonneg_of_pos hxnonneg hepsilon)
    exact (Real.continuousAt_log (ne_of_gt hfx)).continuousWithinAt
  rw [logMatrix_apply, ← (epsilonRegularize_posDef B hB hepsilon).isHermitian.cfc_eq]
  rw [hregularizedCfc]
  rw [← cfc_comp' (p := IsSelfAdjoint) Real.log f B hlogContinuous
    (ha := hB.isHermitian)]
  rw [hB.isHermitian.cfc_eq]
  congr 2
  funext x
  dsimp [f]
  rw [div_eq_mul_inv]
  congr 1
  ring
end QEC.Semantics.FiniteMatrixEntropy

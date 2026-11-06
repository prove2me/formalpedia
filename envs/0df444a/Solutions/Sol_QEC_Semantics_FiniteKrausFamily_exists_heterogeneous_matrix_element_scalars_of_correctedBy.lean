-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.exists_heterogeneous_matrix_element_scalars_of_correctedBy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:56:13.636096+00:00
-- url     : https://prove2.me/submissions/3481e99e-3552-4bb3-b550-a2cd25cdcff0

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_recovery_branch_mem_span_of_heterogeneous_correctedBy
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_operator_scalar_on_code_of_forall_mem_span
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
noncomputable section
open QEC
open QEC.Semantics
open Classical
open DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v w
open QEC.Semantics.FiniteKrausFamily
variable {H : Type u} {K : Type u} {ι : Type v} {κ : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [Fintype ι] [Fintype κ]
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.solution
    (E : FiniteKrausFamily ι H K) (C : QuantumCode H)
    (R : κ → K →ₗ[Complex] H)
    (hR_complete : ∑ r : κ, (LinearMap.adjoint (R r)).comp (R r) = 1)
    (hcorrect : ∀ rho : DensityOperator H,
      DensityOperator.SupportedOn C rho →
        (∑ r : κ, (R r).comp
          ((E.inducedMap rho.toOperator).comp (LinearMap.adjoint (R r)))) =
          rho.toOperator) :
    ∃ scalar : ι → ι → Complex,
      ∀ i j (x : H), x ∈ C.carrier → ∀ y : H, y ∈ C.carrier →
        inner Complex (E.operator i x) (E.operator j y) =
          scalar i j * inner Complex x y := by
  classical
  have hscalar : ∀ r i : _, ∃ a : Complex,
      ∀ x : H, x ∈ C.carrier → R r (E.operator i x) = a • x := by
    intro r i
    exact operator_scalar_on_code_of_forall_mem_span ((R r).comp (E.operator i)) C
      (fun x hx => recovery_branch_mem_span_of_heterogeneous_correctedBy
        E C R hcorrect r i hx)
  choose a ha using hscalar
  refine ⟨fun i j => ∑ r : κ, star (a r i) * a r j, ?_⟩
  intro i j x hx y hy
  calc
    inner Complex (E.operator i x) (E.operator j y) =
        inner Complex (E.operator i x)
          ((∑ r : κ, (LinearMap.adjoint (R r)).comp (R r)) (E.operator j y)) := by
            rw [hR_complete]
            rfl
    _ = ∑ r : κ, inner Complex (R r (E.operator i x)) (R r (E.operator j y)) := by
          rw [LinearMap.sum_apply]
          change inner Complex (E.operator i x)
            (∑ r : κ, LinearMap.adjoint (R r) (R r (E.operator j y))) = _
          rw [inner_sum]
          apply Finset.sum_congr rfl
          intro r _
          exact LinearMap.adjoint_inner_right (𝕜 := Complex)
            (R r) (E.operator i x) (R r (E.operator j y))
    _ = ∑ r : κ, (star (a r i) * a r j) * inner Complex x y := by
          apply Finset.sum_congr rfl
          intro r _
          rw [ha r i x hx, ha r j y hy]
          simp
          ring
    _ = (∑ r : κ, star (a r i) * a r j) * inner Complex x y := by
          rw [Finset.sum_mul]
end QEC.Semantics.FiniteKrausFamily

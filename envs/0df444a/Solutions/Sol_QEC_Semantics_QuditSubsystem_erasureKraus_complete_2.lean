-- Prove2me | solution 2 for QEC.Semantics.QuditSubsystem.erasureKraus_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:20:23.554303+00:00
-- url     : https://prove2.me/submissions/bc736760-d9df-42d4-9c99-e851508199c4

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Theorems.Thm_QEC_Semantics_QuditSubsystem_prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch_reference
import Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocal_one_reference
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_Correctable_unitaryTransport
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
import Theorems.Thm_QEC_Semantics_KnillLaflamme_unitaryTransport
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
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (S : QuditSubsystem q) :
    (S.erasureKraus).Complete := by
  let b := stdOrthonormalBasis Complex S.selectedSystem
  have hfactorized : S.erasureFactorizedKraus.Complete := by
    rw [FiniteKrausFamily.Complete]
    calc
      ∑ a, (LinearMap.adjoint (S.erasureFactorizedKraus.operator a)).comp
          (S.erasureFactorizedKraus.operator a) =
          ∑ a, S.extendLocal (InnerProductSpace.rankOne Complex (b a) (b a)).toLinearMap := by
            apply Finset.sum_congr rfl
            intro a _
            simpa only [erasureFactorizedKraus, LinearMap.adjoint_adjoint] using
              S.prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch_reference
                (b a) (b a)
      _ = S.extendLocal (∑ a,
          (InnerProductSpace.rankOne Complex (b a) (b a)).toLinearMap) := by
            symm
            unfold QuditSubsystem.extendLocal
            induction (Finset.univ : Finset (Fin (Module.finrank Complex S.selectedSystem)))
                using Finset.induction_on with
            | empty => simp
            | insert a s ha ih =>
                rw [Finset.sum_insert ha, TensorProduct.map_add_left, ih,
                  Finset.sum_insert ha]
      _ = S.extendLocal 1 := by
            congr 1
            simpa [Module.End.one_eq_id] using congrArg ContinuousLinearMap.toLinearMap
              (OrthonormalBasis.sum_rankOne_eq_id b)
      _ = 1 := S.extendLocal_one_reference
  change (S.erasureFactorizedKraus.unitaryTransport S.registerFactorization.symm
    (identityTransport S.complementSystem)).Complete
  exact S.erasureFactorizedKraus.unitaryTransport_complete S.registerFactorization.symm
    (identityTransport S.complementSystem) hfactorized
end QEC.Semantics.QuditSubsystem

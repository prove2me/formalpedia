-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.firstCut_exists_unique_active_leftIsotypicSector_of_nonzero_code_QECertChecked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:12:24.180547+00:00
-- url     : https://prove2.me/submissions/fdc75e2b-f9c4-467f-9451-9612ccaacf52

import Definitions.Def_QEC_Import_Compact_9b62ca70080600a3
import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCut_overlap_commute
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutProjectorMC_isSymmetric
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_doubleInteractionCoefficient_commutes_leftIsotypicSector
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_exists_nonzero_doubleInteractionCoefficient_of_ne_zero
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutGlobalCoordinateTransport_conj_fullCodeProjector
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCodeLift_sector_dichotomy_QECertChecked
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCut_doubleInteractionCoefficient_sector_dichotomy
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCodeLift_sector_eq_zero_implies_doubleInteractionCoefficient_zero
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCut_doubleInteractionCoefficient_sector_eq_zero_implies_codeLift_sector_eq_zero
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_exists_unique_active_leftIsotypicSector
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
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
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_eq_self_of_mem
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorizationWithReference_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceReordering_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceTransport_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.mem_regionSubsystem_selected_iff
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.regionSubsystem_selected
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
attribute [local simp] QEC.Semantics.QuditSubsystem.registerFactorizationWithReference_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceReordering_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceTransport_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.firstCut_exists_unique_active_leftIsotypicSector_of_nonzero_code_QECertStatement.{v} := by
  unfold QEC.Bounds.BPTCommutingProjectorModel.firstCut_exists_unique_active_leftIsotypicSector_of_nonzero_code_QECertStatement
  intro «L» «kappa» «compact_inst_2» «M» «region» «hcode» «hC»
  have hfullNonzero : M.fullCodeProjector ≠ 0 := by
    intro hzero
    apply hcode
    apply le_antisymm
    · intro vector hvector
      have hfixed : M.fullCodeProjector vector = vector :=
        M.codeSpace.projector_eq_self_of_mem hvector
      rw [hzero] at hfixed
      simpa using hfixed.symm
    · exact bot_le
  have hcodeLiftNonzero : M.firstCutCodeLift region ≠ 0 := by
    intro hzero
    apply hfullNonzero
    calc
      M.fullCodeProjector =
          (M.firstCutGlobalCoordinateTransport region).symm.conjOperator
            ((M.firstCutGlobalCoordinateTransport region).conjOperator
              M.fullCodeProjector) :=
        (M.firstCutGlobalCoordinateTransport region).symm_conjOperator_conjOperator _ |>.symm
      _ = (M.firstCutGlobalCoordinateTransport region).symm.conjOperator
            (M.firstCutCodeLift region) := by
        rw [M.firstCutGlobalCoordinateTransport_conj_fullCodeProjector]
      _ = (M.firstCutGlobalCoordinateTransport region).symm.conjOperator 0 :=
        congrArg (M.firstCutGlobalCoordinateTransport region).symm.conjOperator hzero
      _ = 0 := by simp [Semantics.UnitaryTransport.conjOperator]
  rcases exists_nonzero_doubleInteractionCoefficient_of_ne_zero
    (M.firstCutCodeLift region) hcodeLiftNonzero with ⟨d, d', a, a', hcoefficient⟩
  have hself : LinearMap.adjoint (M.firstCutProjectorMC region) =
      M.firstCutProjectorMC region := by
    apply LinearMap.isSelfAdjoint_iff'.mp
    exact (LinearMap.isSymmetric_iff_isSelfAdjoint _).mp
      (M.firstCutProjectorMC_isSymmetric region)
  have hover : Commute
      (overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region))
      (overlapLiftRight
        (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (M.fourFactorProjectorCDLocal region)) :=
    M.firstCut_overlap_commute region
  let coefficient := M.firstCutDoubleInteractionCoefficient region d d' a a'
  have hcoefficient' : coefficient ≠ 0 := by
    change leftInteractionCoefficient
      (rightInteractionCoefficient (M.firstCutCodeLift region) d d') a a' ≠ 0
    exact hcoefficient
  have hcommute : ∀ component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region),
      Commute coefficient
        (leftIsotypicSectorProjector (M.firstCutProjectorMC region) component) := by
    intro component
    simpa [coefficient, firstCutDoubleInteractionCoefficient, firstCutCodeLift] using
      (doubleInteractionCoefficient_commutes_leftIsotypicSector
        (M.firstCutProjectorMC region) (M.fourFactorProjectorCDLocal region)
        hself hover component d d' a a')
  have hsector : ∀ component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region),
      coefficient * leftIsotypicSectorProjector (M.firstCutProjectorMC region) component = 0 ∨
        coefficient * leftIsotypicSectorProjector (M.firstCutProjectorMC region) component =
          coefficient := by
    intro component
    simpa [coefficient] using
      M.firstCut_doubleInteractionCoefficient_sector_dichotomy
        region hC component d d' a a'
  rcases exists_unique_active_leftIsotypicSector
    (M.firstCutProjectorMC region) coefficient hcoefficient' hcommute hsector with
    ⟨component, hactive, hother⟩
  refine ⟨component, ?_, ?_⟩
  · rcases M.firstCutCodeLift_sector_dichotomy_QECertChecked region hC component with hzero | hfull
    · exfalso
      have hvanish : coefficient *
          leftIsotypicSectorProjector (M.firstCutProjectorMC region) component = 0 := by
        change M.firstCutDoubleInteractionCoefficient region d d' a a' *
          leftIsotypicSectorProjector (M.firstCutProjectorMC region) component = 0
        exact M.firstCutCodeLift_sector_eq_zero_implies_doubleInteractionCoefficient_zero
          region component d d' a a' hzero
      rw [hactive] at hvanish
      exact hcoefficient' hvanish
    · exact hfull
  · intro other hne
    have hvanish : coefficient *
        leftIsotypicSectorProjector (M.firstCutProjectorMC region) other = 0 :=
      hother other hne
    change M.firstCutCodeLift region * M.firstCutSectorLift region other = 0
    apply M.firstCut_doubleInteractionCoefficient_sector_eq_zero_implies_codeLift_sector_eq_zero
      region hC other d d' a a' hcoefficient'
    change coefficient * leftIsotypicSectorProjector (M.firstCutProjectorMC region) other = 0
    exact hvanish
end QEC.Bounds.BPTCommutingProjectorModel

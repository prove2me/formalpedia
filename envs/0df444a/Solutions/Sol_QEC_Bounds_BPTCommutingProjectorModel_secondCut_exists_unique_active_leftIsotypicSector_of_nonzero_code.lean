-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCut_exists_unique_active_leftIsotypicSector_of_nonzero_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:41:25.796087+00:00
-- url     : https://prove2.me/submissions/d70e1049-bce6-4fc9-a80a-6d22c65ea1ea

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutGlobalCoordinateTransport_conj_fullCodeProjector
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutProjectorAB_isSymmetric
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_overlap_commute
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCodeLift_sector_dichotomy
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_doubleInteractionCoefficient_sector_dichotomy
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCodeLift_sector_eq_zero_implies_doubleInteractionCoefficient_zero
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_doubleInteractionCoefficient_sector_eq_zero_implies_codeLift_sector_eq_zero
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_doubleInteractionCoefficient_commutes_leftIsotypicSector
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_exists_nonzero_doubleInteractionCoefficient_of_ne_zero
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
theorem _root_.solution
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hM : M.RegionErasureRecoverable region) :
    ∃ component : isotypicComponents
        (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
        (M.fourFactorB region),
      M.secondCutCodeLift region * M.secondCutSectorLift region component =
          M.secondCutCodeLift region ∧
        ∀ other : isotypicComponents
            (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
            (M.fourFactorB region),
          other ≠ component →
          M.secondCutCodeLift region * M.secondCutSectorLift region other = 0 := by
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
  have hcodeLiftNonzero : M.secondCutCodeLift region ≠ 0 := by
    intro hzero
    apply hfullNonzero
    calc
      M.fullCodeProjector =
          (M.secondCutGlobalCoordinateTransport region).symm.conjOperator
            ((M.secondCutGlobalCoordinateTransport region).conjOperator
              M.fullCodeProjector) :=
        (M.secondCutGlobalCoordinateTransport region).symm_conjOperator_conjOperator _ |>.symm
      _ = (M.secondCutGlobalCoordinateTransport region).symm.conjOperator
            (M.secondCutCodeLift region) := by
        rw [M.secondCutGlobalCoordinateTransport_conj_fullCodeProjector]
      _ = (M.secondCutGlobalCoordinateTransport region).symm.conjOperator 0 :=
        congrArg (M.secondCutGlobalCoordinateTransport region).symm.conjOperator hzero
      _ = 0 := by simp [Semantics.UnitaryTransport.conjOperator]
  rcases exists_nonzero_doubleInteractionCoefficient_of_ne_zero
    (M.secondCutCodeLift region) hcodeLiftNonzero with ⟨cd, cd', a, a', hcoefficient⟩
  have hself : LinearMap.adjoint (M.fourFactorProjectorABLocal region) =
      M.fourFactorProjectorABLocal region := by
    apply LinearMap.isSelfAdjoint_iff'.mp
    exact (LinearMap.isSymmetric_iff_isSelfAdjoint _).mp
      (M.secondCutProjectorAB_isSymmetric region)
  have hover : Commute
      (overlapLiftLeft
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
        (M.fourFactorProjectorABLocal region))
      (overlapLiftRight (A := M.fourFactorA region)
        (M.secondCutProjectorBbarM region)) :=
    M.secondCut_overlap_commute region
  let coefficient := M.secondCutDoubleInteractionCoefficient region cd cd' a a'
  have hcoefficient' : coefficient ≠ 0 := by
    change leftInteractionCoefficient
      (rightInteractionCoefficient (M.secondCutCodeLift region) cd cd') a a' ≠ 0
    exact hcoefficient
  have hcommute : ∀ component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region),
      Commute coefficient
        (leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component) := by
    intro component
    simpa [coefficient, secondCutDoubleInteractionCoefficient, secondCutCodeLift] using
      (doubleInteractionCoefficient_commutes_leftIsotypicSector
        (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region)
        hself hover component cd cd' a a')
  have hsector : ∀ component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region),
      coefficient * leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component = 0 ∨
        coefficient * leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component =
          coefficient := by
    intro component
    simpa [coefficient] using
      M.secondCut_doubleInteractionCoefficient_sector_dichotomy
        region hM component cd cd' a a'
  rcases exists_unique_active_leftIsotypicSector
    (M.fourFactorProjectorABLocal region) coefficient hcoefficient' hcommute hsector with
    ⟨component, hactive, hother⟩
  refine ⟨component, ?_, ?_⟩
  · rcases M.secondCutCodeLift_sector_dichotomy region hM component with hzero | hfull
    · exfalso
      have hvanish : coefficient *
          leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component = 0 := by
        change M.secondCutDoubleInteractionCoefficient region cd cd' a a' *
          leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component = 0
        exact M.secondCutCodeLift_sector_eq_zero_implies_doubleInteractionCoefficient_zero
          region component cd cd' a a' hzero
      rw [hactive] at hvanish
      exact hcoefficient' hvanish
    · exact hfull
  · intro other hne
    have hvanish : coefficient *
        leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) other = 0 :=
      hother other hne
    change M.secondCutCodeLift region * M.secondCutSectorLift region other = 0
    apply M.secondCut_doubleInteractionCoefficient_sector_eq_zero_implies_codeLift_sector_eq_zero
      region hM other cd cd' a a' hcoefficient'
    change coefficient * leftIsotypicSectorProjector
      (M.fourFactorProjectorABLocal region) other = 0
    exact hvanish
end QEC.Bounds.BPTCommutingProjectorModel

-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.firstCut_externalBoundary_sector_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:57:44.691545+00:00
-- url     : https://prove2.me/submissions/2bad06d4-0ef2-4744-a1e1-e594d6d26fca

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_local_commutingProjection_codeSector_eq_zero_or_codeProjector
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCoordinateTransport_conj_source_overlap_product
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCut_overlap_commute
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutProjectorMC_isSymmetric
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCoordinateTransport_symm_conj_externalBoundaryLift
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_conjOperator_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_commute_of_conjOperator_commute
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorMap_isSymmetricProjection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_one_isSymmetricProjection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_composeUnitaryTransport_conjOperator
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_leftIsotypicSectorProjector_commutes_overlap
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_leftIsotypicSectorProjector_isSymmetricProjection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionErasureRecoverable_implies_noInformationOn
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorAssociatorUnitary_symm_conj_tensorMap
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
    (hC : M.RegionErasureRecoverable (M.externalBoundary region))
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)) :
    M.fullCodeProjector *
        (M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
          ((M.fourFactorCCoordinateRelabel region).symm.conjOperator
            (leftIsotypicSectorProjector (M.firstCutProjectorMC region) component)) = 0 ∨
    M.fullCodeProjector *
        (M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
          ((M.fourFactorCCoordinateRelabel region).symm.conjOperator
            (leftIsotypicSectorProjector (M.firstCutProjectorMC region) component)) =
      M.fullCodeProjector := by
  let A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)
  let C := M.fourFactorC region
  let D := M.fourFactorD region
  let P : Semantics.Operator (Semantics.CompositeSystem A C) := M.firstCutProjectorMC region
  let Q : Semantics.Operator (Semantics.CompositeSystem C D) :=
    M.fourFactorProjectorCDLocal region
  let sector : Semantics.Operator C := leftIsotypicSectorProjector P component
  let Zx : Semantics.Operator L.Register :=
    (M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
      ((M.fourFactorCCoordinateRelabel region).symm.conjOperator sector)
  let U := M.firstCutCoordinateTransport region
  let V := M.fourFactorTransport region
  let H := composeUnitaryTransport V U.symm
  let sectorLift : Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem A C) D) :=
    overlapLiftLeft (C := D) (TensorProduct.map (1 : Semantics.Operator A) sector)
  let codeLift : Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem A C) D) :=
    overlapLiftLeft (C := D) P * overlapLiftRight (A := A) Q
  have hself : LinearMap.adjoint P = P := by
    apply LinearMap.isSelfAdjoint_iff'.mp
    apply (LinearMap.isSymmetric_iff_isSelfAdjoint P).mp
    simpa [P] using M.firstCutProjectorMC_isSymmetric region
  have hover : Commute (overlapLiftLeft (C := D) P) (overlapLiftRight (A := A) Q) := by
    simpa [A, C, D, P, Q] using M.firstCut_overlap_commute region
  have hsectorCommutes := leftIsotypicSectorProjector_commutes_overlap
    P Q hself hover component
  have hPcommutes : Commute (overlapLiftLeft (C := D) P) sectorLift := by
    change TensorProduct.map P (1 : Semantics.Operator D) *
        TensorProduct.map (TensorProduct.map (1 : Semantics.Operator A) sector)
          (1 : Semantics.Operator D) =
      TensorProduct.map (TensorProduct.map (1 : Semantics.Operator A) sector)
          (1 : Semantics.Operator D) * TensorProduct.map P (1 : Semantics.Operator D)
    rw [← TensorProduct.map_mul, ← TensorProduct.map_mul]
    simpa using congrArg (fun operator =>
      TensorProduct.map operator (1 : Semantics.Operator D)) hsectorCommutes.1.eq
  have hsectorLiftRight : sectorLift =
      overlapLiftRight (A := A) (TensorProduct.map sector (1 : Semantics.Operator D)) := by
    dsimp [sectorLift, overlapLiftLeft, overlapLiftRight]
    symm
    exact tensorAssociatorUnitary_symm_conj_tensorMap
      (1 : Semantics.Operator A) sector (1 : Semantics.Operator D)
  have hQcommutes : Commute (overlapLiftRight (A := A) Q) sectorLift := by
    rw [hsectorLiftRight]
    change
      (tensorAssociatorUnitary A C D).symm.conjOperator
          (TensorProduct.map (1 : Semantics.Operator A) Q) *
        (tensorAssociatorUnitary A C D).symm.conjOperator
          (TensorProduct.map (1 : Semantics.Operator A)
            (TensorProduct.map sector (1 : Semantics.Operator D))) =
      (tensorAssociatorUnitary A C D).symm.conjOperator
          (TensorProduct.map (1 : Semantics.Operator A)
            (TensorProduct.map sector (1 : Semantics.Operator D))) *
        (tensorAssociatorUnitary A C D).symm.conjOperator
          (TensorProduct.map (1 : Semantics.Operator A) Q)
    calc
      (tensorAssociatorUnitary A C D).symm.conjOperator
          (TensorProduct.map (1 : Semantics.Operator A) Q) *
          (tensorAssociatorUnitary A C D).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A)
              (TensorProduct.map sector (1 : Semantics.Operator D))) =
          (tensorAssociatorUnitary A C D).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A) Q *
              TensorProduct.map (1 : Semantics.Operator A)
                (TensorProduct.map sector (1 : Semantics.Operator D))) :=
          (Semantics.UnitaryTransport.conjOperator_mul _ _ _).symm
      _ = (tensorAssociatorUnitary A C D).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A)
              (TensorProduct.map sector (1 : Semantics.Operator D)) *
              TensorProduct.map (1 : Semantics.Operator A) Q) := by
          congr 1
          rw [← TensorProduct.map_mul, ← TensorProduct.map_mul]
          simpa using congrArg (fun operator =>
            TensorProduct.map (1 : Semantics.Operator A) operator) hsectorCommutes.2.eq
      _ = (tensorAssociatorUnitary A C D).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A)
              (TensorProduct.map sector (1 : Semantics.Operator D))) *
          (tensorAssociatorUnitary A C D).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A) Q) :=
          Semantics.UnitaryTransport.conjOperator_mul _ _ _
  have hcodeLiftCommutes : Commute codeLift sectorLift := by
    exact (hPcommutes.symm.mul_right hQcommutes.symm).symm
  have hsectorProjection : sector.IsSymmetricProjection := by
    simpa [sector, P] using
      leftIsotypicSectorProjector_isSymmetricProjection P component
  have hsectorLiftProjection : sectorLift.IsSymmetricProjection := by
    dsimp [sectorLift, overlapLiftLeft]
    exact tensorMap_isSymmetricProjection
      (tensorMap_isSymmetricProjection (one_isSymmetricProjection A) hsectorProjection)
      (one_isSymmetricProjection D)
  have hHsector : H.conjOperator Zx = sectorLift := by
    change (composeUnitaryTransport (M.fourFactorTransport region)
      (M.firstCutCoordinateTransport region).symm).conjOperator
        ((M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
          ((M.fourFactorCCoordinateRelabel region).symm.conjOperator sector)) = sectorLift
    rw [composeUnitaryTransport_conjOperator]
    simpa [A, C, D, sectorLift] using
      M.firstCutCoordinateTransport_symm_conj_externalBoundaryLift region sector
  have hHcode : H.conjOperator M.fullCodeProjector = codeLift := by
    change (composeUnitaryTransport (M.fourFactorTransport region)
      (M.firstCutCoordinateTransport region).symm).conjOperator M.fullCodeProjector = codeLift
    rw [composeUnitaryTransport_conjOperator]
    calc
      (M.firstCutCoordinateTransport region).symm.conjOperator
          ((M.fourFactorTransport region).conjOperator M.fullCodeProjector) =
          (M.firstCutCoordinateTransport region).symm.conjOperator
            ((M.firstCutCoordinateTransport region).conjOperator codeLift) := by
        congr 1
        simpa [A, C, D, codeLift, P, Q] using
          (M.firstCutCoordinateTransport_conj_source_overlap_product region).symm
      _ = codeLift :=
        (M.firstCutCoordinateTransport region).symm_conjOperator_conjOperator codeLift
  have hZxProjection : Zx.IsSymmetricProjection := by
    apply (isSymmetricProjection_conjOperator_iff H Zx).mp
    rw [hHsector]
    exact hsectorLiftProjection
  have hcodeCommutes : Commute M.fullCodeProjector Zx := by
    apply commute_of_conjOperator_commute H
    rw [hHcode, hHsector]
    exact hcodeLiftCommutes
  have hlocal : (M.regionSubsystem (M.externalBoundary region)).OperatorSupportedOnRegister Zx := by
    refine ⟨(M.fourFactorCCoordinateRelabel region).symm.conjOperator sector, ?_⟩
    rfl
  have hInformation := M.regionErasureRecoverable_implies_noInformationOn
    (M.externalBoundary region) hC
  simpa [Zx, fullCodeProjector] using
    (local_commutingProjection_codeSector_eq_zero_or_codeProjector
      (M.regionSubsystem (M.externalBoundary region)) M.codeSpace hInformation hlocal
      hZxProjection hcodeCommutes)
end QEC.Bounds.BPTCommutingProjectorModel

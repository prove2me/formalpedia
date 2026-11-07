-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCut_all_leftLocal_scalar_compression_of_region_recoverable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:17:23.57199+00:00
-- url     : https://prove2.me/submissions/b816909e-95af-4e1e-9fc0-66820fb7dbdb

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_LeftProjection
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_LeftPhysical
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionErasureRecoverable_implies_noInformationOn
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutGlobalCoordinateTransport_conj_fullCodeProjector
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutGlobalCoordinateTransport_conj_regionLift
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_noInformationOn_iff_allLocalScalarCompression
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
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hM : M.RegionErasureRecoverable region)
    (E : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) :
    ∃ scalar : Complex,
      M.secondCutCodeLift region *
          overlapLiftLeft
            (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) E *
          M.secondCutCodeLift region = scalar • M.secondCutCodeLift region := by
  let A := M.regionSubsystem (M.interior region)
  let AB := M.regionSubsystem region
  let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
  have hAAB : A.selected ⊆ AB.selected := by
    intro site hsite
    exact (Finset.mem_sdiff.mp hsite).1
  let split := A.selectedFactorization AB hAAB
  let Elocal : Semantics.Operator AB.selectedSystem := split.symm.conjOperator E
  let Ephysical : Semantics.Operator L.Register := AB.extendLocalToRegister Elocal
  let G := M.secondCutGlobalCoordinateTransport region
  let R := M.secondCutCodeLift region
  have hInformation := M.regionErasureRecoverable_implies_noInformationOn region hM
  have hAll := (AB.noInformationOn_iff_allLocalScalarCompression M.codeSpace).mp hInformation
  rcases hAll Elocal with ⟨scalar, hscalar⟩
  have hscalar' : M.fullCodeProjector * Ephysical * M.fullCodeProjector =
      scalar • M.fullCodeProjector := by
    change (M.fullCodeProjector.comp Ephysical).comp M.fullCodeProjector = _
    rw [LinearMap.comp_assoc]
    exact hscalar
  have hGcode : G.conjOperator M.fullCodeProjector = R := by
    simpa [G, R] using M.secondCutGlobalCoordinateTransport_conj_fullCodeProjector region
  have hGlocal : G.conjOperator Ephysical = overlapLiftLeft (C := CD) E := by
    calc
      G.conjOperator Ephysical = overlapLiftLeft (C := CD) (split.conjOperator Elocal) := by
        simpa [G, Ephysical] using
          M.secondCutGlobalCoordinateTransport_conj_regionLift region Elocal
      _ = overlapLiftLeft (C := CD) E := by
        rw [show split.conjOperator Elocal = E by
          simpa [Elocal] using split.conjOperator_symm_conjOperator E]
  refine ⟨scalar, ?_⟩
  calc
    R * overlapLiftLeft (C := CD) E * R =
        G.conjOperator M.fullCodeProjector * G.conjOperator Ephysical *
          G.conjOperator M.fullCodeProjector := by
      simpa only [hGcode, hGlocal]
    _ = G.conjOperator (M.fullCodeProjector * Ephysical * M.fullCodeProjector) := by
      calc
        G.conjOperator M.fullCodeProjector * G.conjOperator Ephysical *
            G.conjOperator M.fullCodeProjector =
            G.conjOperator (M.fullCodeProjector * Ephysical) *
              G.conjOperator M.fullCodeProjector :=
          congrArg (fun operator => operator * G.conjOperator M.fullCodeProjector)
            (Semantics.UnitaryTransport.conjOperator_mul G M.fullCodeProjector Ephysical).symm
        _ = G.conjOperator ((M.fullCodeProjector * Ephysical) * M.fullCodeProjector) :=
          (Semantics.UnitaryTransport.conjOperator_mul G
            (M.fullCodeProjector * Ephysical) M.fullCodeProjector).symm
        _ = G.conjOperator (M.fullCodeProjector * Ephysical * M.fullCodeProjector) := rfl
    _ = G.conjOperator (scalar • M.fullCodeProjector) :=
      congrArg G.conjOperator hscalar'
    _ = scalar • G.conjOperator M.fullCodeProjector := by
      exact G.conjOperatorLinearMap.map_smul scalar M.fullCodeProjector
    _ = scalar • R := by simpa only [hGcode]
end QEC.Bounds.BPTCommutingProjectorModel

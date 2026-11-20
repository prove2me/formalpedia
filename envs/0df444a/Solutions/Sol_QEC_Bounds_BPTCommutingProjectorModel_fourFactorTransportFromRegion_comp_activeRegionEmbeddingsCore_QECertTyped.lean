-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransportFromRegion_comp_activeRegionEmbeddingsCore_QECertTyped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:43:45.510457+00:00
-- url     : https://prove2.me/submissions/c8dc060f-6862-43d7-a517-be23c550d229

import Definitions.Def_QEC_Import_Typed_123b7341367dacca
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_SelectedEmbeddingCore
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_ComplementEmbeddingCore
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_Embeddings
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_activeComplementEmbeddingCore_apply_tmul_QECertChecked
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_activeSelectedEmbeddingCore_apply_tmul_QECertChecked
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicSectorBlockTransportLeft_toLinearEquiv_apply_tmul_of_apply_eq
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorEmbeddingLeft_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorEmbeddingRight_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_productBlockRegrouping_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_productBlockRegrouping_apply_tmul_tmul
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
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_toLinearEquiv_apply_tmul_of_apply_eq
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorEmbeddingLeft_apply_tmul
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorEmbeddingRight_apply_tmul
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.mem_regionSubsystem_selected_iff
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.productBlockRegrouping_apply_tmul
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.productBlockRegrouping_apply_tmul_tmul
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


section
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
private theorem linearMap_ext_sixTensorFactors
    {A W N X N2 D Y : Type u}
    [AddCommMonoid A] [Module Complex A]
    [AddCommMonoid W] [Module Complex W]
    [AddCommMonoid N] [Module Complex N]
    [AddCommMonoid X] [Module Complex X]
    [AddCommMonoid N2] [Module Complex N2]
    [AddCommMonoid D] [Module Complex D]
    [AddCommMonoid Y] [Module Complex Y]
    {f g : (((A ⊗[Complex] W) ⊗[Complex] N) ⊗[Complex]
      (X ⊗[Complex] (N2 ⊗[Complex] D))) →ₗ[Complex] Y}
    (h : ∀ a w n x n2 d,
      f (((a ⊗ₜ[Complex] w) ⊗ₜ[Complex] n) ⊗ₜ[Complex]
        (x ⊗ₜ[Complex] (n2 ⊗ₜ[Complex] d))) =
      g (((a ⊗ₜ[Complex] w) ⊗ₜ[Complex] n) ⊗ₜ[Complex]
        (x ⊗ₜ[Complex] (n2 ⊗ₜ[Complex] d)))) :
    f = g := by
  ext a w n x n2 d
  exact h a w n x n2 d
set_option maxHeartbeats 1600000 in
private theorem fourFactorTransportFromRegion_apply_activePreimages
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (a : M.fourFactorA region) (b : M.fourFactorB region)
    (c : M.fourFactorC region) (d : M.fourFactorD region) :
    M.fourFactorTransportFromRegion region
        ((M.regionSubsystem region).registerFactorization.symm
          (((M.regionSubsystem (M.interior region)).selectedFactorization
            (M.regionSubsystem region)
            (by
              intro site hsite
              exact (Finset.mem_sdiff.mp hsite).1)).symm
            (a ⊗ₜ[Complex] b) ⊗ₜ[Complex]
          ((M.regionSubsystem region).complementFactorization
            (M.regionSubsystem (region ∪ M.externalBoundary region))
            (by
              intro site hsite
              exact Finset.mem_union_left _ hsite)).symm
            (c ⊗ₜ[Complex] d))) =
      a ⊗ₜ[Complex] (b ⊗ₜ[Complex] (c ⊗ₜ[Complex] d)) := by
  simp [fourFactorTransportFromRegion, composeUnitaryTransport,
    unitaryRTensor, unitaryLTensor, tensorAssociatorUnitary]
set_option maxHeartbeats 1600000 in
private theorem jointActiveCoordinates_apply_productBlock
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (a : M.fourFactorA region) (w : WB.restrictScalars Complex)
    (nB' : isotypicLiftedMultiplicity.{0} nB) (x : WC.restrictScalars Complex)
    (nC' : isotypicLiftedMultiplicity.{0} nC) (d : M.fourFactorD region) :
    (fourFactorJointBCSectorEmbedding (A := M.fourFactorA region)
      (D := M.fourFactorD region) (bcomponent.1.restrictScalars Complex)
      (ccomponent.1.restrictScalars Complex))
        ((M.secondCutJointActiveBlockTransport
          region bcomponent ccomponent WB WC UB UC).symm
          ((tensorAssociatorUnitary
            (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
            (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
              (WC.restrictScalars Complex))
            (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
              (M.fourFactorD region)))
            ((productBlockRegrouping (A := M.fourFactorA region)
              (W := WB.restrictScalars Complex) (N := isotypicLiftedMultiplicity.{0} nB)
              (X := WC.restrictScalars Complex)
              (D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
                (M.fourFactorD region))).symm
              (((a ⊗ₜ[Complex] w) ⊗ₜ[Complex] nB') ⊗ₜ[Complex]
                (x ⊗ₜ[Complex] (nC' ⊗ₜ[Complex] d)))))) =
      a ⊗ₜ[Complex]
        ((bcomponent.1.restrictScalars Complex).subtype
          (UB.symm (w ⊗ₜ[Complex] nB')) ⊗ₜ[Complex]
        ((ccomponent.1.restrictScalars Complex).subtype
          (UC.symm (x ⊗ₜ[Complex] nC')) ⊗ₜ[Complex] d)) := by
  simp [secondCutJointActiveBlockTransport, productBlockRegrouping,
    fourFactorJointBCSectorEmbedding, jointBCSectorEmbeddingRight,
    isotypicSectorBlockTransportLeft, composeUnitaryTransport,
    unitaryRTensor, unitaryLTensor, tensorAssociatorUnitary]
universe projectionInputLeft projectionInputRight projectionImageLeft projectionImageRight
  projectionRegistered projectionPhysical
private theorem apply_composed_tensorMap_of_preimages
    {SL : Type projectionInputLeft} {SR : Type projectionInputRight}
    {TL : Type projectionImageLeft} {TR : Type projectionImageRight}
    {Z : Type projectionRegistered} {Y : Type projectionPhysical}
    [AddCommMonoid SL] [Module Complex SL]
    [AddCommMonoid SR] [Module Complex SR]
    [AddCommMonoid TL] [Module Complex TL]
    [AddCommMonoid TR] [Module Complex TR]
    [AddCommMonoid Z] [Module Complex Z]
    [AddCommMonoid Y] [Module Complex Y]
    (transport : Z →ₗ[Complex] Y) (registration : (TL ⊗[Complex] TR) →ₗ[Complex] Z)
    (selected : SL →ₗ[Complex] TL) (complement : SR →ₗ[Complex] TR)
    (left : SL) (right : SR) (leftPreimage : TL) (rightPreimage : TR) (value : Y)
    (left_eq : selected left = leftPreimage) (right_eq : complement right = rightPreimage)
    (projected : transport (registration (leftPreimage ⊗ₜ[Complex] rightPreimage)) = value) :
    (transport.comp (registration.comp (TensorProduct.map selected complement)))
      (left ⊗ₜ[Complex] right) = value := by
  calc
    _ = transport (registration (selected left ⊗ₜ[Complex] complement right)) := rfl
    _ = transport (registration (leftPreimage ⊗ₜ[Complex] rightPreimage)) := by
      rw [left_eq, right_eq]
    _ = value := projected
set_option maxHeartbeats 1600000 in
private theorem physicalActiveCoordinates_apply_productBlock
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (a : M.fourFactorA region) (w : WB.restrictScalars Complex)
    (nB' : isotypicLiftedMultiplicity.{0} nB) (x : WC.restrictScalars Complex)
    (nC' : isotypicLiftedMultiplicity.{0} nC) (d : M.fourFactorD region) :
    ((M.fourFactorTransportFromRegion region).toLinearEquiv.toLinearMap.comp
      ((M.regionSubsystem region).registerFactorization.symm.toLinearEquiv.toLinearMap.comp
        (TensorProduct.map
          (M.activeSelectedEmbeddingCore region bcomponent WB UB).toLinearMap
          (M.activeComplementEmbeddingCore region ccomponent WC UC).toLinearMap)))
        (((a ⊗ₜ[Complex] w) ⊗ₜ[Complex] nB') ⊗ₜ[Complex]
          (x ⊗ₜ[Complex] (nC' ⊗ₜ[Complex] d))) =
      a ⊗ₜ[Complex]
        ((bcomponent.1.restrictScalars Complex).subtype
          (UB.symm (w ⊗ₜ[Complex] nB')) ⊗ₜ[Complex]
        ((ccomponent.1.restrictScalars Complex).subtype
          (UC.symm (x ⊗ₜ[Complex] nC')) ⊗ₜ[Complex] d)) := by
  let b : M.fourFactorB region :=
    (bcomponent.1.restrictScalars Complex).subtype (UB.symm (w ⊗ₜ[Complex] nB'))
  let c : M.fourFactorC region :=
    (ccomponent.1.restrictScalars Complex).subtype (UC.symm (x ⊗ₜ[Complex] nC'))
  let selectedInput := (a ⊗ₜ[Complex] w) ⊗ₜ[Complex] nB'
  let complementInput := x ⊗ₜ[Complex] (nC' ⊗ₜ[Complex] d)
  let selected := (M.activeSelectedEmbeddingCore region bcomponent WB UB).toLinearMap
  let complement := (M.activeComplementEmbeddingCore region ccomponent WC UC).toLinearMap
  let registration := (M.regionSubsystem region).registerFactorization.symm.toLinearEquiv.toLinearMap
  let transport := (M.fourFactorTransportFromRegion region).toLinearEquiv.toLinearMap
  let selectedPreimage :=
    ((M.regionSubsystem (M.interior region)).selectedFactorization
      (M.regionSubsystem region)
      (by
        intro site hsite
        exact (Finset.mem_sdiff.mp hsite).1)).symm (a ⊗ₜ[Complex] b)
  let complementPreimage :=
    ((M.regionSubsystem region).complementFactorization
      (M.regionSubsystem (region ∪ M.externalBoundary region))
      (by
        intro site hsite
        exact Finset.mem_union_left _ hsite)).symm (c ⊗ₜ[Complex] d)
  let value := a ⊗ₜ[Complex] (b ⊗ₜ[Complex] (c ⊗ₜ[Complex] d))
  have left_eq : selected selectedInput = selectedPreimage := rfl
  have right_eq : complement complementInput = complementPreimage := rfl
  have projected : transport (registration (selectedPreimage ⊗ₜ[Complex] complementPreimage)) = value :=
    M.fourFactorTransportFromRegion_apply_activePreimages region a b c d
  exact apply_composed_tensorMap_of_preimages transport registration selected complement
    selectedInput complementInput selectedPreimage complementPreimage value left_eq right_eq projected
end BPTCommutingProjectorModel
end Bounds
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 4000000
namespace QEC.Bounds.BPTCommutingProjectorModel
private noncomputable def qecertSharedEmbeddingProof123b7341367dacca
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC))) :
    (M.fourFactorTransportFromRegion region).toLinearEquiv.toLinearMap.comp
        ((M.regionSubsystem region).registerFactorization.symm.toLinearEquiv.toLinearMap.comp
          (TensorProduct.map
            (M.activeSelectedEmbeddingCore region bcomponent WB UB).toLinearMap
            (M.activeComplementEmbeddingCore region ccomponent WC UC).toLinearMap)) =
      (fourFactorJointBCSectorEmbedding (A := M.fourFactorA region)
        (D := M.fourFactorD region) (bcomponent.1.restrictScalars Complex)
        (ccomponent.1.restrictScalars Complex)).comp
        ((M.secondCutJointActiveBlockTransport
          region bcomponent ccomponent WB WC UB UC).symm.toLinearEquiv.toLinearMap.comp
          ((tensorAssociatorUnitary
            (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
            (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
              (WC.restrictScalars Complex))
            (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
              (M.fourFactorD region))).toLinearEquiv.toLinearMap.comp
            (productBlockRegrouping (A := M.fourFactorA region)
              (W := WB.restrictScalars Complex) (N := isotypicLiftedMultiplicity.{0} nB)
              (X := WC.restrictScalars Complex)
              (D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
                (M.fourFactorD region))).symm.toLinearEquiv.toLinearMap)) := by
  refine linearMap_ext_sixTensorFactors
    (A := M.fourFactorA region) (W := WB.restrictScalars Complex)
    (N := isotypicLiftedMultiplicity.{0} nB) (X := WC.restrictScalars Complex)
    (N2 := isotypicLiftedMultiplicity.{0} nC) (D := M.fourFactorD region) ?_
  intro a w nBVector x nCVector d
  exact (physicalActiveCoordinates_apply_productBlock
    M region bcomponent ccomponent WB WC UB UC a w nBVector x nCVector d).trans
      (jointActiveCoordinates_apply_productBlock
        M region bcomponent ccomponent WB WC UB UC a w nBVector x nCVector d).symm

theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransportFromRegion_comp_activeRegionEmbeddingsCore_QECertTypedStatement.{v} :=
  @qecertSharedEmbeddingProof123b7341367dacca

end QEC.Bounds.BPTCommutingProjectorModel

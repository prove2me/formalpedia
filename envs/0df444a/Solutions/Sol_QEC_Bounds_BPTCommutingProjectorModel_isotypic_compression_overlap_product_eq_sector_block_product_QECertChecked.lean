-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.isotypic_compression_overlap_product_eq_sector_block_product_QECertChecked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:12:24.175065+00:00
-- url     : https://prove2.me/submissions/32058ba5-d02b-42d8-9b34-f0c71f7b988d

import Definitions.Def_QEC_Import_Compact_622cd611c7503a95
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Embedding
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_tensorTripleSubtypeEmbedding_comp_tensorTripleSubtypeEmbedding
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorTripleSubtypeEmbedding_comp_adjoint_eq_leftIsotypicSectorLift_QECertChecked
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_tensorTripleSubtypeEmbedding_comp_overlapLiftLeft_comp_tensorTripleSubtypeEmbedding_QECertChecked
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_tensorTripleSubtypeEmbedding_comp_overlapLiftRight_comp_tensorTripleSubtypeEmbedding_QECertChecked
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_leftIsotypicSectorProjector_commutes_overlap
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
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
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.isotypic_compression_overlap_product_eq_sector_block_product_QECertStatement.{u} := by
  unfold QEC.Bounds.BPTCommutingProjectorModel.isotypic_compression_overlap_product_eq_sector_block_product_QECertStatement
  intro «A» «B» «C» «compact_inst_3» «compact_inst_4» «compact_inst_5» «compact_inst_6» «compact_inst_7» «compact_inst_8» «compact_inst_9» «compact_inst_10» «compact_inst_11» «P» «Q» «hselfAdjoint» «hcommute» «component»
  let p : Submodule Complex B := component.1.restrictScalars Complex
  let J := tensorTripleSubtypeEmbedding (A := A) (C := C) p
  let E := LinearMap.adjoint J
  let L := overlapLiftLeft (C := C) P
  let K := overlapLiftRight (A := A) Q
  let S := overlapLiftLeft (C := C)
    (TensorProduct.map (1 : Semantics.Operator A)
      (leftIsotypicSectorProjector P component))
  have hJE : J.comp E = S := by
    dsimp [J, E, S, p]
    exact tensorTripleSubtypeEmbedding_comp_adjoint_eq_leftIsotypicSectorLift_QECertChecked P component
  have hEJ : E.comp J =
      (1 : Semantics.Operator (Semantics.CompositeSystem
        (Semantics.CompositeSystem A p) C)) := by
    dsimp [E, J]
    exact adjoint_tensorTripleSubtypeEmbedding_comp_tensorTripleSubtypeEmbedding
      (A := A) (C := C) p
  have hsectorLiftRight : S =
      overlapLiftRight (A := A)
        (TensorProduct.map (leftIsotypicSectorProjector P component)
          (1 : Semantics.Operator C)) := by
    dsimp [S, overlapLiftLeft, overlapLiftRight]
    symm
    exact tensorAssociatorUnitary_symm_conj_tensorMap
      (1 : Semantics.Operator A) (leftIsotypicSectorProjector P component)
      (1 : Semantics.Operator C)
  have hlocal : Commute Q
      (TensorProduct.map (leftIsotypicSectorProjector P component)
        (1 : Semantics.Operator C)) :=
    (leftIsotypicSectorProjector_commutes_overlap P Q hselfAdjoint hcommute component).2
  have hKS : Commute K S := by
    rw [hsectorLiftRight]
    change Commute
      ((tensorAssociatorUnitary A B C).symm.conjOperator
        (TensorProduct.map (1 : Semantics.Operator A) Q))
      ((tensorAssociatorUnitary A B C).symm.conjOperator
        (TensorProduct.map (1 : Semantics.Operator A)
          (TensorProduct.map (leftIsotypicSectorProjector P component)
            (1 : Semantics.Operator C))))
    calc
      (tensorAssociatorUnitary A B C).symm.conjOperator
          (TensorProduct.map (1 : Semantics.Operator A) Q) *
        (tensorAssociatorUnitary A B C).symm.conjOperator
          (TensorProduct.map (1 : Semantics.Operator A)
            (TensorProduct.map (leftIsotypicSectorProjector P component)
              (1 : Semantics.Operator C))) =
          (tensorAssociatorUnitary A B C).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A) Q *
              TensorProduct.map (1 : Semantics.Operator A)
                (TensorProduct.map (leftIsotypicSectorProjector P component)
                  (1 : Semantics.Operator C))) :=
        (Semantics.UnitaryTransport.conjOperator_mul _ _ _).symm
      _ = (tensorAssociatorUnitary A B C).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A)
              (TensorProduct.map (leftIsotypicSectorProjector P component)
                (1 : Semantics.Operator C)) *
              TensorProduct.map (1 : Semantics.Operator A) Q) := by
          congr 1
          rw [← TensorProduct.map_mul, ← TensorProduct.map_mul]
          simpa using congrArg (fun operator =>
            TensorProduct.map (1 : Semantics.Operator A) operator) hlocal.eq
      _ = (tensorAssociatorUnitary A B C).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A)
              (TensorProduct.map (leftIsotypicSectorProjector P component)
                (1 : Semantics.Operator C))) *
          (tensorAssociatorUnitary A B C).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A) Q) :=
        Semantics.UnitaryTransport.conjOperator_mul _ _ _
  have hScompK : S.comp K = K.comp S := by
    simpa only [Module.End.mul_eq_comp] using hKS.eq.symm
  have hSonJ : S.comp J = J := by
    calc
      S.comp J = (J.comp E).comp J := by rw [hJE]
      _ = J.comp (E.comp J) := by rw [LinearMap.comp_assoc]
      _ = J.comp (1 : Semantics.Operator
          (Semantics.CompositeSystem (Semantics.CompositeSystem A p) C)) := by rw [hEJ]
      _ = J := by
        apply LinearMap.ext
        intro vector
        rfl
  have hS_K_J : S.comp (K.comp J) = K.comp J := by
    calc
      S.comp (K.comp J) = (S.comp K).comp J := by rw [LinearMap.comp_assoc]
      _ = (K.comp S).comp J := congrArg (fun operator => operator.comp J) hScompK
      _ = K.comp (S.comp J) := by rw [LinearMap.comp_assoc]
      _ = K.comp J := by rw [hSonJ]
  have hleftCompression : E.comp (L.comp J) =
      overlapLiftLeft (C := C) (overlapProjectorOnIsotypicComponent P component) := by
    dsimp [E, L, J, p]
    exact
      adjoint_tensorTripleSubtypeEmbedding_comp_overlapLiftLeft_comp_tensorTripleSubtypeEmbedding_QECertChecked
        P component
  have hrightCompression : E.comp (K.comp J) =
      overlapLiftRight (A := A)
        (overlapRightProjectorOnIsotypicComponent P Q component) := by
    dsimp [E, K, J, p]
    exact
      adjoint_tensorTripleSubtypeEmbedding_comp_overlapLiftRight_comp_tensorTripleSubtypeEmbedding_QECertChecked
        P Q component
  have hraw : E.comp ((L * K).comp J) =
      (E.comp (L.comp J)) * (E.comp (K.comp J)) := by
    apply LinearMap.ext
    intro vector
    change E (L (K (J vector))) = E (L (J (E (K (J vector)))))
    have hcore : J (E (K (J vector))) = K (J vector) := by
      have happly := congrArg (fun operator => operator vector) hS_K_J
      calc
        J (E (K (J vector))) = S (K (J vector)) := by
          have hJEapply := congrArg (fun operator => operator (K (J vector))) hJE
          simpa only [LinearMap.comp_apply] using hJEapply
        _ = K (J vector) := by
          simpa only [LinearMap.comp_apply] using happly
    rw [hcore]
  change E.comp ((L * K).comp J) =
    overlapLiftLeft (C := C) (overlapProjectorOnIsotypicComponent P component) *
      overlapLiftRight (A := A)
        (overlapRightProjectorOnIsotypicComponent P Q component)
  calc
    E.comp ((L * K).comp J) = (E.comp (L.comp J)) * (E.comp (K.comp J)) := hraw
    _ = overlapLiftLeft (C := C) (overlapProjectorOnIsotypicComponent P component) *
        overlapLiftRight (A := A)
          (overlapRightProjectorOnIsotypicComponent P Q component) := by
        exact congrArg₂ (fun left right => left * right)
          hleftCompression hrightCompression
end QEC.Bounds.BPTCommutingProjectorModel

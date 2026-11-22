-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyReassociatedEmbedding_compression_regionLocal_QECertTypedV3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T03:24:22.05028+00:00
-- url     : https://prove2.me/submissions/df658da4-725f-4562-aaae-b157ac2b09fe

import Definitions.Def_QEC_Import_Typed_f4213f714e8dcefe_V3
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalAssemblyAssociator_symm_conj_leftMap_right_one_QECertTyped
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalAssemblyOutputEmbedding_compression_regionLocal_QECertTyped
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicSectorBlockTransportLeft_toLinearEquiv_apply_tmul_of_apply_eq
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorEmbeddingLeft_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorEmbeddingRight_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_productBlockRegrouping_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_productBlockRegrouping_apply_tmul_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Bounds_compression_precompose_unitary_of_eq
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
set_option autoImplicit false
noncomputable section
open QEC QEC.Bounds Classical
open scoped BigOperators ComplexOrder TensorProduct
universe v
open QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyReassociatedEmbedding_compression_regionLocal_QECertTypedStatementV3.{v} := by
  intro L kappa inst M region bcomponent ccomponent nB nC hB hC WB WC UB UC A
  dsimp only [QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyReassociatedEmbedding_compression_regionLocal_QECertTypedStatementV3Body, QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyReassociatedEmbedding_compression_regionLocal_QECertTypedStatementV3Core]
  intro O hO Enew hEnew
  let F := M.fourFactorTransport region
  let S := Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)
  let N := isotypicLiftedMultiplicity.{0} nB
  let X := WC.restrictScalars Complex
  let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
    (M.fourFactorD region)
  let E := M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC
  let eSel := (M.activeSelectedEmbedding region bcomponent WB UB).toLinearMap
  let A0 : Semantics.Operator (Semantics.CompositeSystem S N) :=
    (LinearMap.adjoint eSel).comp (A.comp eSel)
  have hRaw := M.finalAssemblyOutputEmbedding_compression_regionLocal_QECertTyped
    region bcomponent ccomponent WB WC UB UC A
  calc
    (LinearMap.adjoint Enew).comp
        ((F.conjOperator ((M.regionSubsystem region).extendLocalToRegister A)).comp Enew) =
      O.symm.conjOperator
        ((LinearMap.adjoint E).comp
          ((F.conjOperator ((M.regionSubsystem region).extendLocalToRegister A)).comp E)) := by
            apply compression_precompose_unitary_of_eq O E Enew
            exact hEnew
    _ = O.symm.conjOperator
        (TensorProduct.map A0 (1 : Semantics.Operator (Semantics.CompositeSystem X D))) := by
          apply congrArg O.symm.conjOperator
          exact hRaw
    _ = TensorProduct.map (TensorProduct.map A0 (1 : Semantics.Operator X))
        (1 : Semantics.Operator D) := by
          subst O
          apply M.finalAssemblyAssociator_symm_conj_leftMap_right_one_QECertTyped
            (nB := nB) (nC := nC) region WB WC

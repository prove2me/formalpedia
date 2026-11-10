-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.xLocal_horizontal_dual_incidence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:45:24.778069+00:00
-- url     : https://prove2.me/submissions/980a6380-e2f9-4bb0-8e3b-a3d8b613d559

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalGridParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0DoubleCylinderEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0DoubleCylinderVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0StarEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0StarVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0SubdivisionEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0SubdivisionVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4DoubleCylinderEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4DoubleCylinderVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4StarEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4StarVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4SubdivisionEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4SubdivisionVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_qDoubleCylinderEndRestriction_apply
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_copiedQ_image_copy
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_copiedQ_image_vertical
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_verticalZ_image_copy
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_verticalZ_image_vertical
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_historicalZeroSyndromeInput_supportFitsRadiusTwo
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorOperator_adjoint_eq_self
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorSupport_eq_support
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_term_adjoint_eq_self
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridOccupiedCells_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_qubitsInRectangle_iff
import Theorems.Thm_QEC_Locality_centeredRectangleClippedGrowthRadius_zero
import Theorems.Thm_QEC_Locality_mem_centeredRectangleQubits_iff
import Theorems.Thm_QEC_Locality_mem_longInteractionEndpointQubits_iff
import Theorems.Thm_QEC_Locality_mem_longNeighborsOf_iff
import Theorems.Thm_QEC_Locality_mem_squareQubits_iff
import Theorems.Thm_QEC_Locality_squareGrowthRadius_succ_sub
import Theorems.Thm_QEC_Locality_squareGrowthRadius_zero
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.alternatingCarrier_zero
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_target_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_target_val
attribute [local simp] QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderEndInclusion_apply
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ0DoubleCylinderEdge_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ0DoubleCylinderVertex_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ0StarEdge_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ0StarVertex_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ0SubdivisionEdge_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ0SubdivisionVertex_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ4DoubleCylinderEdge_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ4DoubleCylinderVertex_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ4StarEdge_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ4StarVertex_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ4SubdivisionEdge_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ4SubdivisionVertex_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.qDoubleCylinderEndRestriction_apply
attribute [local simp] QEC.Coding.BDL26XLocalConnectingWeight.copiedQ_image_copy
attribute [local simp] QEC.Coding.BDL26XLocalConnectingWeight.copiedQ_image_vertical
attribute [local simp] QEC.Coding.BDL26XLocalConnectingWeight.verticalZ_image_copy
attribute [local simp] QEC.Coding.BDL26XLocalConnectingWeight.verticalZ_image_vertical
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.MultiscaleDecoder.historicalZeroSyndromeInput_supportFitsRadiusTwo
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.interactionLength_sym2_mk
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_diag_not_mem_fixedGeneratorInteractions
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorOperator_adjoint_eq_self
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorSupport_eq_support
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.term_adjoint_eq_self
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
attribute [local simp] QEC.Locality.MarkedSeparatorSpine.exposedSide_stop
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_gridCellQubits_iff
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_gridOccupiedCells_iff
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff
attribute [local simp] QEC.Locality.centeredRectangleClippedGrowthRadius_zero
attribute [local simp] QEC.Locality.mem_centeredRectangleQubits_iff
attribute [local simp] QEC.Locality.mem_longInteractionEndpointQubits_iff
attribute [local simp] QEC.Locality.mem_longNeighborsOf_iff
attribute [local simp] QEC.Locality.mem_squareQubits_iff
attribute [local simp] QEC.Locality.squareGrowthRadius_succ_sub
attribute [local simp] QEC.Locality.squareGrowthRadius_zero
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
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
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


section
namespace QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity
open BDL26XLocalConnectingWeight
open scoped BigOperators Classical
private theorem xLocal_inner_horizontal_eq_iff
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f g : XStarFace P x) (i a : Fin S.half) (j : Fin (S.half - 1))
    (b : Fin (S.half + 1)) :
    (Sum.inr (Sum.inl (f, i, j)) : SubdivisionEdge P x S) =
        subdivisionHorizontalEdge P x S g a b ↔
      f = g ∧ i = a ∧ j.val + 1 = b.val := by
  unfold subdivisionHorizontalEdge
  split_ifs with hb0 hbm
  · simp only [Sum.inr_ne_inl, false_iff, not_and]
    intro _ _ he
    omega
  · simp only [Sum.inr_ne_inl, false_iff, not_and]
    intro _ _ he
    have := j.isLt
    omega
  · simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, Fin.ext_iff]
    change (f = g ∧ i.val = a.val ∧ j.val = b.val - 1) ↔
      f = g ∧ i.val = a.val ∧ j.val + 1 = b.val
    constructor <;> rintro ⟨hf, hi, hj⟩ <;> exact ⟨hf, hi, by omega⟩
private theorem xLocal_inner_horizontal_ne_vertical
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f g : XStarFace P x) (i b : Fin S.half) (j : Fin (S.half - 1))
    (a : Fin (S.half + 1)) :
    (Sum.inr (Sum.inl (f, i, j)) : SubdivisionEdge P x S) ≠
      subdivisionVerticalEdge P x S g a b := by
  unfold subdivisionVerticalEdge
  split_ifs <;> simp
end QEC.Coding.BDL26RXLocalReplacement
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity
open BDL26XLocalConnectingWeight
open scoped BigOperators Classical
namespace QEC.Coding.BDL26RXLocalReplacement
theorem _root_.solution
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f : XStarFace P x) (i : Fin S.half) (j : Fin (S.half - 1))
    (target : SubdivisionFace P x S) :
    subdivisionFaceEdgeMatrix P x S (Sum.inr (Sum.inl (f, i, j))) target =
      (if target = (f, i, stripStart S.half j) then 1 else 0) +
        (if target = (f, i, stripEnd S.half j) then 1 else 0) := by
  rcases target with ⟨g, a, b⟩
  have hstart : (f = g ∧ i = a ∧ j.val + 1 = b.val + 1) ↔
      (g, a, b) = (f, i, stripStart S.half j) := by
    simp only [Prod.mk.injEq, Fin.ext_iff, stripStart]
    constructor <;> rintro ⟨hf, hi, hj⟩ <;> exact ⟨hf.symm, hi.symm, by omega⟩
  have hend : (f = g ∧ i = a ∧ j.val + 1 = b.val) ↔
      (g, a, b) = (f, i, stripEnd S.half j) := by
    simp only [Prod.mk.injEq, Fin.ext_iff, stripEnd]
    constructor <;> rintro ⟨hf, hi, hj⟩ <;> exact ⟨hf.symm, hi.symm, by omega⟩
  simp only [subdivisionFaceEdgeMatrix, xLocal_inner_horizontal_eq_iff,
    xLocal_inner_horizontal_ne_vertical, ite_false, add_zero]
  change (if f = g ∧ i = a ∧ j.val + 1 = b.val then 1 else 0) +
      (if f = g ∧ i = a ∧ j.val + 1 = b.val + 1 then 1 else 0) = _
  simp only [hend, hstart, add_comm]
end QEC.Coding.BDL26RXLocalReplacement

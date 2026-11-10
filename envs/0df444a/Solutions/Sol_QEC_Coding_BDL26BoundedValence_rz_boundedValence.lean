-- Prove2me | solution 1 for QEC.Coding.BDL26BoundedValence.rz_boundedValence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:18:58.34585+00:00
-- url     : https://prove2.me/submissions/78bd3fcf-8e41-423e-a272-daacaff07ada

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_rx_boundedValence
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_boundedValence_transpose
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_correctionRegion_mem
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_syndromeRegion_mem
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rx_boundedValence
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzFace_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzQ_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzX_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzZ_card
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
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_qToZDoubleCylinderEdge_end
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_qToZDoubleCylinderEdge_start
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
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
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
attribute [local simp] QEC.Coding.BDL26DecodingGraph.correctionRegion_mem
attribute [local simp] QEC.Coding.BDL26DecodingGraph.syndromeRegion_mem
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.alternatingCarrier_zero
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_target_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_target_val
attribute [local simp] QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderEndInclusion_apply
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzFace_card
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzQ_card
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzX_card
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzZ_card
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
namespace QEC.Coding.BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26RXLocalReplacement
open BDL26TannerLocalRegularity
private theorem xq_face_exists (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (x : P.X) (q : P.Q) (h : P.xq x q = true) :
    ∃ f : P.Face, ∃ c : Fin 2, P.faceX f = x ∧ P.faceQ f c = q := by
  let z := A.qzRoot q
  let shared : SharedQ P.data x z.1 := ⟨q, by simp [h, z.2]⟩
  obtain ⟨⟨f, c⟩, hc⟩ := (P.perfectPairing x z.1).2 shared
  exact ⟨f.1, c, f.2.1, congrArg Subtype.val hc⟩
private theorem qz_face_exists (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (z : P.Z) (h : P.qz q z = true) :
    ∃ f : P.Face, ∃ c : Fin 2, P.faceQ f c = q ∧ P.faceZ f = z := by
  let x := A.xqRoot q
  let shared : SharedQ P.data x.1 z := ⟨q, by simp [x.2, h]⟩
  obtain ⟨⟨f, c⟩, hc⟩ := (P.perfectPairing x.1 z).2 shared
  exact ⟨f.1, c, congrArg Subtype.val hc, f.2.2⟩
private theorem qToZEdge_eq_rxRaw (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale)
    (q : P.Q) (z : P.Z) (h : P.qz q z = true)
    (edge : QDoubleCylinderEdge (transposePresentation P) q S) :
    qToZDoubleCylinderEdge P A q z h S edge =
      qToXDoubleCylinderEdgeRaw (transposePresentation P) q z h S edge := by
  cases edge <;> rfl
private theorem rzFaceToRX_z (P : TannerSquarePresentation)
    (S : OddScale) (f : BDL26RZLocalReplacement.RZFace P S) :
    rxFaceZ (transposePresentation P) S (rzFaceToRX P S f) =
      BDL26RZLocalReplacement.rzFaceX P S f := by
  rcases f with localFace | glue | oldFace <;> rfl
private theorem rzFaceToRX_q (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale)
    (f : BDL26RZLocalReplacement.RZFace P S) (c : Fin 2) :
    rxFaceQ (transposePresentation P) S (rzFaceToRX P S f) c =
      BDL26RZLocalReplacement.rzFaceQ P A S f c := by
  rcases f with ⟨z, cell, first, second⟩ | ⟨edge, cylinderEdge, endpoint⟩ | oldFace
  · rcases cell with copyFace | rectangle
    all_goals fin_cases first <;> fin_cases second <;> fin_cases c <;> rfl
  · fin_cases c
    · change (Sum.inl ⟨edge.1.2, qToXDoubleCylinderEdgeRaw (transposePresentation P)
        edge.1.1 edge.1.2 edge.2 S cylinderEdge⟩ : RX1 (transposePresentation P) S) =
        Sum.inl ⟨edge.1.2, qToZDoubleCylinderEdge P A
          edge.1.1 edge.1.2 edge.2 S cylinderEdge⟩
      rw [qToZEdge_eq_rxRaw]
    · rfl
  · rfl
private theorem rzFaceToRX_x (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale)
    (f : BDL26RZLocalReplacement.RZFace P S) :
    rxFaceX (transposePresentation P) S (rzFaceToRX P S f) =
      BDL26RZLocalReplacement.rzFaceZ P A S f := by
  rcases f with ⟨z, cell, first, second⟩ | ⟨edge, cylinderEdge, endpoint⟩ | oldFace
  · rcases cell with copyFace | rectangle
    all_goals fin_cases first <;> fin_cases second <;> rfl
  · fin_cases endpoint
    · change (⟨edge.1.2, tannerDoubleCylinderEdgeStart (transposePresentation P)
        edge.1.2 S (qToXDoubleCylinderEdgeRaw (transposePresentation P)
          edge.1.1 edge.1.2 edge.2 S cylinderEdge)⟩ : RX0 (transposePresentation P) S) =
        ⟨edge.1.2, qToZDoubleCylinderVertex P A edge.1.1 edge.1.2 edge.2 S
          (qDoubleCylinderEdgeStart (transposePresentation P) edge.1.1 S cylinderEdge)⟩
      rw [qToZDoubleCylinderEdge_start, qToZEdge_eq_rxRaw]
    · change (⟨edge.1.2, tannerDoubleCylinderEdgeEnd (transposePresentation P)
        edge.1.2 S (qToXDoubleCylinderEdgeRaw (transposePresentation P)
          edge.1.1 edge.1.2 edge.2 S cylinderEdge)⟩ : RX0 (transposePresentation P) S) =
        ⟨edge.1.2, qToZDoubleCylinderVertex P A edge.1.1 edge.1.2 edge.2 S
          (qDoubleCylinderEdgeEnd (transposePresentation P) edge.1.1 S cylinderEdge)⟩
      rw [qToZDoubleCylinderEdge_end, qToZEdge_eq_rxRaw]
  · rfl
private theorem rz_xq_to_rx_qz (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (x : BDL26RZLocalReplacement.RZX P S)
    (q : BDL26RZLocalReplacement.RZQ P S)
    (h : BDL26RZLocalReplacement.rzXQIncidence P A4.toTannerSquareAdmissible S x q = true) :
    rxQZIncidence (transposePresentation P) S q x = true := by
  let successor := BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S
  let admissible := BDL26RZLocalReplacement.rzReplacementAdmissibleV4 P A4 R S
  obtain ⟨f, c, hx, hq⟩ := xq_face_exists successor admissible.toTannerSquareAdmissible x q h
  apply (rxQZIncidence_eq_true_iff (transposePresentation P) S q x).2
  exact ⟨rzFaceToRX P S f, c,
    (rzFaceToRX_q P A4.toTannerSquareAdmissible S f c).trans hq,
    (rzFaceToRX_z P S f).trans hx⟩
private theorem rz_qz_to_rx_xq (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (q : BDL26RZLocalReplacement.RZQ P S)
    (z : BDL26RZLocalReplacement.RZZ P S)
    (h : BDL26RZLocalReplacement.rzQZIncidence P A4.toTannerSquareAdmissible S q z = true) :
    rxXQIncidence (transposePresentation P) S z q = true := by
  let successor := BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S
  let admissible := BDL26RZLocalReplacement.rzReplacementAdmissibleV4 P A4 R S
  obtain ⟨f, c, hq, hz⟩ := qz_face_exists successor admissible.toTannerSquareAdmissible q z h
  apply (rxXQIncidence_eq_true_iff (transposePresentation P) S z q).2
  exact ⟨rzFaceToRX P S f, c,
    (rzFaceToRX_x P A4.toTannerSquareAdmissible S f).trans hz,
    (rzFaceToRX_q P A4.toTannerSquareAdmissible S f c).trans hq⟩
private theorem rz_xDegree_le_rx_zDegree (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (x : BDL26RZLocalReplacement.RZX P S) :
    xDegree (BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S) x ≤
      zDegree (rxReplacementPresentation (transposePresentation P) S) x := by
  classical
  let source := BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S
  let target := rxReplacementPresentation (transposePresentation P) S
  let f : {v : source.Q // source.xq x v = true} →
      {v : target.Q // target.qz v x = true} :=
    fun v => ⟨v.1, rz_xq_to_rx_qz P A4 R S x v.1 v.2⟩
  exact Fintype.card_le_of_injective f (fun a b h =>
    Subtype.ext (congrArg (fun v : {v : target.Q // target.qz v x = true} => v.1) h))
private theorem rz_zDegree_le_rx_xDegree (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (z : BDL26RZLocalReplacement.RZZ P S) :
    zDegree (BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S) z ≤
      xDegree (rxReplacementPresentation (transposePresentation P) S) z := by
  classical
  let source := BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S
  let target := rxReplacementPresentation (transposePresentation P) S
  let f : {v : source.Q // source.qz v z = true} →
      {v : target.Q // target.xq z v = true} :=
    fun v => ⟨v.1, rz_qz_to_rx_xq P A4 R S v.1 z v.2⟩
  exact Fintype.card_le_of_injective f (fun a b h =>
    Subtype.ext (congrArg (fun v : {v : target.Q // target.xq z v = true} => v.1) h))
private theorem rz_qXDegree_le_rx_qZDegree (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (q : BDL26RZLocalReplacement.RZQ P S) :
    qXDegree (BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S) q ≤
      qZDegree (rxReplacementPresentation (transposePresentation P) S) q := by
  classical
  let source := BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S
  let target := rxReplacementPresentation (transposePresentation P) S
  let f : {v : source.X // source.xq v q = true} →
      {v : target.Z // target.qz q v = true} :=
    fun v => ⟨v.1, rz_xq_to_rx_qz P A4 R S v.1 q v.2⟩
  exact Fintype.card_le_of_injective f (fun a b h =>
    Subtype.ext (congrArg (fun v : {v : target.Z // target.qz q v = true} => v.1) h))
private theorem rz_qZDegree_le_rx_qXDegree (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (q : BDL26RZLocalReplacement.RZQ P S) :
    qZDegree (BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S) q ≤
      qXDegree (rxReplacementPresentation (transposePresentation P) S) q := by
  classical
  let source := BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S
  let target := rxReplacementPresentation (transposePresentation P) S
  let f : {v : source.Z // source.qz q v = true} →
      {v : target.X // target.xq v q = true} :=
    fun v => ⟨v.1, rz_qz_to_rx_xq P A4 R S q v.1 v.2⟩
  exact Fintype.card_le_of_injective f (fun a b h =>
    Subtype.ext (congrArg (fun v : {v : target.X // target.xq v q = true} => v.1) h))
private theorem rz_boundedValence_of_rx (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (hB : BoundedValence (rxReplacementPresentation (transposePresentation P) S)) :
    BoundedValence (BDL26RZLocalReplacement.rzReplacementPresentation
      P A4.toTannerSquareAdmissible S) := by
  classical
  have hx := rz_xDegree_le_rx_zDegree P A4 R S
  have hz := rz_zDegree_le_rx_xDegree P A4 R S
  have hqx := rz_qXDegree_le_rx_qZDegree P A4 R S
  have hqz := rz_qZDegree_le_rx_qXDegree P A4 R S
  refine ⟨fun x => (hx x).trans (hB.2.1 x), fun z => (hz z).trans (hB.1 z), ?_⟩
  intro q
  obtain ⟨hxx, hzz, hsum⟩ := hB.2.2 q
  refine ⟨(hqx q).trans hzz, (hqz q).trans hxx, ?_⟩
  have ha := hqx q
  have hb := hqz q
  omega
end QEC.Coding.BDL26BoundedValence
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26RXLocalReplacement
open BDL26TannerLocalRegularity
namespace QEC.Coding.BDL26BoundedValence
theorem _root_.solution (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (h : BoundedValence P) :
    BoundedValence (BDL26RZLocalReplacement.rzReplacementPresentation
      P A4.toTannerSquareAdmissible S) :=
  rz_boundedValence_of_rx P A4 R S
    (rx_boundedValence (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A4)
      (transposeTannerSquareCellularRegular P R) S (boundedValence_transpose P h))
end QEC.Coding.BDL26BoundedValence

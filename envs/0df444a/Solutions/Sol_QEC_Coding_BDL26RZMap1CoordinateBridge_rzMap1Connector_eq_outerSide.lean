-- Prove2me | solution 1 for QEC.Coding.BDL26RZMap1CoordinateBridge.rzMap1Connector_eq_outerSide
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T15:18:26.777689+00:00
-- url     : https://prove2.me/submissions/e7cfddb1-98b6-4c67-abff-d6ec67fa9d69

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
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
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
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
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
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
namespace QEC
namespace Coding
namespace BDL26RZMap1CoordinateBridge
open scoped BigOperators
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
open BDL26RZLocalReplacement
open MultiscaleDecoder
attribute [local instance] rzQFintype
attribute [local instance] subdivisionEdgeDecidableEq
universe u
private theorem pathChain_horizontalPrefixPath
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (step : Nat) (hstep : step ≤ S.half) :
    pathChain (horizontalPrefixPath P x S face step hstep) =
      ∑ i : Fin step, canonicalBasisWord
        (subdivisionHorizontalEdge P x S face
          ⟨i.1, lt_of_lt_of_le i.2 hstep⟩ 0) := by
  classical
  induction step with
  | zero =>
      change (0 : Word Field (SubdivisionEdge P x S)) = _
      simp
  | succ step ih =>
      change pathChain (horizontalPrefixPath P x S face step (by omega)) +
        Pi.single (subdivisionHorizontalEdge P x S face ⟨step, by omega⟩ 0) 1 = _
      rw [ih]
      rw [Fin.sum_univ_castSucc]
      congr 1
      ext coordinate
      simp [canonicalBasisWord, Pi.single_apply]
private theorem pathChain_verticalPrefixPath
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (step : Nat) (hstep : step ≤ S.half) :
    pathChain (verticalPrefixPath P x S face step hstep) =
      ∑ j : Fin step, canonicalBasisWord
        (subdivisionVerticalEdge P x S face 0
          ⟨j.1, lt_of_lt_of_le j.2 hstep⟩) := by
  classical
  induction step with
  | zero =>
      change (0 : Word Field (SubdivisionEdge P x S)) = _
      simp
  | succ step ih =>
      change pathChain (verticalPrefixPath P x S face step (by omega)) +
        Pi.single (subdivisionVerticalEdge P x S face 0 ⟨step, by omega⟩) 1 = _
      rw [ih]
      rw [Fin.sum_univ_castSucc]
      congr 1
      ext coordinate
      simp [canonicalBasisWord, Pi.single_apply]
private theorem pathChain_map
    {Vertex Edge Vertex' Edge' : Type}
    [Fintype Edge] [Fintype Edge'] [DecidableEq Edge] [DecidableEq Edge']
    {edgeStart edgeEnd : Edge → Vertex}
    {edgeStart' edgeEnd' : Edge' → Vertex'}
    (vertexMap : Vertex → Vertex') (edgeMap : Edge → Edge')
    (start_commutes : ∀ edge, edgeStart' (edgeMap edge) =
      vertexMap (edgeStart edge))
    (end_commutes : ∀ edge, edgeEnd' (edgeMap edge) =
      vertexMap (edgeEnd edge))
    {root target : Vertex}
    (path : UndirectedPath edgeStart edgeEnd root target) :
    pathChain
        (UndirectedPath.map vertexMap edgeMap start_commutes end_commutes path) =
      wordPushforward edgeMap (pathChain path) := by
  classical
  induction path with
  | nil => simp [UndirectedPath.map, pathChain]
  | @step u v path edge connects ih =>
      change
        pathChain
            (UndirectedPath.step
              (UndirectedPath.map vertexMap edgeMap start_commutes end_commutes path)
              (edgeMap edge) _) =
          wordPushforward edgeMap (pathChain path + Pi.single edge 1)
      rw [pathChain, ih, map_add, wordPushforward_single]
private theorem pathChain_eq_of_heq
    {Vertex Edge : Type} [DecidableEq Edge]
    {edgeStart edgeEnd : Edge → Vertex}
    {firstRoot firstTarget secondRoot secondTarget : Vertex}
    (first : UndirectedPath edgeStart edgeEnd firstRoot firstTarget)
    (second : UndirectedPath edgeStart edgeEnd secondRoot secondTarget)
    (hroot : firstRoot = secondRoot) (htarget : firstTarget = secondTarget)
    (hpath : HEq first second) : pathChain first = pathChain second := by
  subst secondRoot
  subst secondTarget
  exact congrArg pathChain (eq_of_heq hpath)
private theorem pathChain_gridPathToCorner_zero
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) :
    pathChain (gridPathToCorner P x S face 0) =
      ∑ i : Fin S.half, canonicalBasisWord
        (subdivisionHorizontalEdge P x S face i 0) := by
  classical
  have hpath : pathChain (gridPathToCorner P x S face 0) =
      pathChain
        (horizontalPrefixPath P x S face S.half (le_refl S.half)) := by
    apply pathChain_eq_of_heq
    · rfl
    · simp [gridLast, gridIndex, twoSelect]
    · change HEq
        (cast (by simp [gridLast, gridIndex, twoSelect])
          (horizontalPrefixPath P x S face S.half (le_refl S.half)))
        (horizontalPrefixPath P x S face S.half (le_refl S.half))
      exact cast_heq _ _
  rw [hpath, pathChain_horizontalPrefixPath]
private theorem pathChain_gridPathToCorner_one
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) :
    pathChain (gridPathToCorner P x S face 1) =
      ∑ j : Fin S.half, canonicalBasisWord
        (subdivisionVerticalEdge P x S face 0 j) := by
  classical
  have hpath : pathChain (gridPathToCorner P x S face 1) =
      pathChain
        (verticalPrefixPath P x S face S.half (le_refl S.half)) := by
    apply pathChain_eq_of_heq
    · rfl
    · simp [gridLast, gridIndex, twoSelect]
    · change HEq
        (cast (by simp [gridLast, gridIndex, twoSelect])
          (verticalPrefixPath P x S face S.half (le_refl S.half)))
        (verticalPrefixPath P x S face S.half (le_refl S.half))
      exact cast_heq _ _
  rw [hpath, pathChain_verticalPrefixPath]
end BDL26RZMap1CoordinateBridge
end Coding
end QEC
end

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZMap1CoordinateBridge
open scoped BigOperators
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
open BDL26RZLocalReplacement
open MultiscaleDecoder
attribute [local instance] QEC.Coding.BDL26RZMap1CoordinateBridge.rzQDecidableEq
attribute [local instance] rzQFintype
attribute [local instance] QEC.Coding.BDL26RZMap1CoordinateBridge.subdivisionEdgeDecidableEq
attribute [local instance] subdivisionEdgeDecidableEq
universe u
namespace QEC.Coding.BDL26RZMap1CoordinateBridge
theorem _root_.solution
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    rzMap1Connector P A4 q z hqz S =
      rzMap1ConnectorOuterSide P A4 q z hqz S := by
  classical
  let owner := rzMap1Owner P A4 q z hqz
  let path := gridPathToCorner (transposePresentation P) z S owner.1 owner.2
  let lifted := UndirectedPath.map
    (edgeStart := subdivisionEdgeStart (transposePresentation P) z S)
    (edgeEnd := subdivisionEdgeEnd (transposePresentation P) z S)
    (edgeStart' := tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
    (edgeEnd' := tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
    (fun vertex => (0, vertex)) (fun edge => Sum.inl (0, edge))
    (fun _ => rfl) (fun _ => rfl) path
  have hconnector : pathChain (rzMap1ConnectorPath P A4 q z hqz S) =
      pathChain lifted := by
    apply pathChain_eq_of_heq
    · have hfaceX := rzMap1Owner_faceX P A4 q z hqz
      simp [rzMap1ZRoot, owner, path, lifted, subdivisionGridVertex,
        xStarFaceXVertex, hfaceX]
    · have htarget := rzMap1Owner_gridCorner P A4 q z hqz S
      rw [show (twoSelect
          (subdivisionGridVertex (transposePresentation P) z S owner.1
            (gridLast S) 0)
          (subdivisionGridVertex (transposePresentation P) z S owner.1
            0 (gridLast S)) owner.2) =
          (subdivisionOriginalBoundaryVertex (transposePresentation P) z S
            (rzMap1QBoundaryVertex P A4 q z hqz)).1 by
        simpa [owner] using htarget]
      exact (qToZDoubleCylinderVertex_qRoot P A4 q z hqz S).symm
    · simp [rzMap1ConnectorPath, owner, path, lifted]
  unfold rzMap1Connector
  rw [hconnector]
  have hlifted : pathChain lifted =
      wordPushforward (fun edge =>
        (Sum.inl (0, edge) : ZDoubleCylinderEdge P z S))
        (pathChain path) := by
    simpa [lifted] using pathChain_map
      (edgeStart := subdivisionEdgeStart (transposePresentation P) z S)
      (edgeEnd := subdivisionEdgeEnd (transposePresentation P) z S)
      (edgeStart' := tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
      (edgeEnd' := tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
      (fun vertex => (0, vertex))
      (fun edge => (Sum.inl (0, edge) : ZDoubleCylinderEdge P z S))
      (fun _ => rfl) (fun _ => rfl) path
  rw [hlifted]
  unfold rzMap1ConnectorOuterSide
  change wordPushforward (fun edge =>
        (Sum.inl (0, edge) : ZDoubleCylinderEdge P z S))
        (pathChain path) =
      twoSelect
        (∑ i : Fin S.half, canonicalBasisWord
          (Sum.inl (0, subdivisionHorizontalEdge (transposePresentation P) z S
            owner.1 i 0) : ZDoubleCylinderEdge P z S))
        (∑ j : Fin S.half, canonicalBasisWord
          (Sum.inl (0, subdivisionVerticalEdge (transposePresentation P) z S
            owner.1 0 j) : ZDoubleCylinderEdge P z S)) owner.2
  dsimp only [path]
  apply twoElim (motive := fun corner =>
      wordPushforward (fun edge =>
        (Sum.inl (0, edge) : ZDoubleCylinderEdge P z S))
          (pathChain (gridPathToCorner (transposePresentation P) z S
            owner.1 corner)) =
        twoSelect
          (∑ i : Fin S.half, canonicalBasisWord
            (Sum.inl (0, subdivisionHorizontalEdge (transposePresentation P)
              z S owner.1 i 0) : ZDoubleCylinderEdge P z S))
          (∑ j : Fin S.half, canonicalBasisWord
            (Sum.inl (0, subdivisionVerticalEdge (transposePresentation P)
              z S owner.1 0 j) : ZDoubleCylinderEdge P z S)) corner)
    (by
      have h := congrArg
        (wordPushforward (fun edge : SubdivisionEdge (transposePresentation P) z S =>
          (Sum.inl (0, edge) : ZDoubleCylinderEdge P z S)))
        (pathChain_gridPathToCorner_zero (transposePresentation P) z S owner.1)
      calc
        _ = _ := h
        _ = _ := by
          rw [map_sum]
          simp [wordPushforward_canonicalBasis, twoSelect])
    (by
      have h := congrArg
        (wordPushforward (fun edge : SubdivisionEdge (transposePresentation P) z S =>
          (Sum.inl (0, edge) : ZDoubleCylinderEdge P z S)))
        (pathChain_gridPathToCorner_one (transposePresentation P) z S owner.1)
      calc
        _ = _ := h
        _ = _ := by
          rw [map_sum]
          simp [wordPushforward_canonicalBasis, twoSelect]) owner.2
end QEC.Coding.BDL26RZMap1CoordinateBridge

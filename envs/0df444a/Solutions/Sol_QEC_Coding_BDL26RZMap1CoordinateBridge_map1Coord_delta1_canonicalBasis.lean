-- Prove2me | solution 1 for QEC.Coding.BDL26RZMap1CoordinateBridge.map1Coord_delta1_canonicalBasis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T15:31:11.353342+00:00
-- url     : https://prove2.me/submissions/b58304b3-b225-45f8-8ffc-536db39e74d7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary0_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_rzMap1Connector_delta1
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_map2Coord_canonicalBasis
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_rzQZIncidence_q_coefficient
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_rzCoboundary1_extendZEdgeWord
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


attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary0_canonicalBasis_apply
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1_canonicalBasis_apply
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.map2Coord_canonicalBasis
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
private theorem field_add_self (value : Field) : value + value = 0 := by
  fin_cases value <;> rfl
private theorem word_add_self {Index : Type} (word : Word Field Index) :
    word + word = 0 := by
  ext index
  exact field_add_self (word index)
private theorem tannerCoboundary1_canonicalBasis_sum
    (P : TannerSquarePresentation) (q : P.Q) :
    tannerCoboundary1 P (canonicalBasisWord q) =
      ∑ z : P.Z, if P.qz q z = true then canonicalBasisWord z else 0 := by
  classical
  ext target
  rw [tannerCoboundary1_canonicalBasis_apply, Finset.sum_apply]
  rw [Finset.sum_eq_single target]
  · by_cases h : P.qz q target = true <;> simp [h, canonicalBasisWord]
  · intro other _ hne
    by_cases h : P.qz q other = true <;>
      simp [h, canonicalBasisWord, hne]
  · intro hnot
    exact (hnot (Finset.mem_univ target)).elim
private theorem successor_delta1_qRoot
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q) :
    tannerCoboundary1
        (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
        (canonicalBasisWord (embedQRoot P S q (rzMap1QRoot P q S))) =
      ∑ z : P.Z, if hqz : P.qz q z = true then
        canonicalBasisWord
          ⟨z, qToZDoubleCylinderVertex P A4.toTannerSquareAdmissible
            q z hqz S (rzMap1QRoot P q S)⟩
      else 0 := by
  classical
  ext target
  rcases target with ⟨z, vertex⟩
  erw [tannerCoboundary1_canonicalBasis_apply]
  change (if rzQZIncidence P A4.toTannerSquareAdmissible S
      (Sum.inr ⟨q, rzMap1QRoot P q S⟩) ⟨z, vertex⟩ = true
    then (1 : Field) else 0) =
    (∑ other : P.Z, if hqz : P.qz q other = true then
      (canonicalBasisWord
        (⟨other, qToZDoubleCylinderVertex P A4.toTannerSquareAdmissible
          q other hqz S (rzMap1QRoot P q S)⟩ : RZZ P S) : Word Field (RZZ P S))
      else 0) ⟨z, vertex⟩
  rw [rzQZIncidence_q_coefficient, Finset.sum_apply]
  rw [Finset.sum_eq_single z]
  · by_cases hqz : P.qz q z = true
    · simp [hqz, vertexIndicator, canonicalBasisWord, Pi.single_apply,
        Sigma.mk.inj_iff, eq_comm]
    · simp [hqz]
  · intro other _ hne
    by_cases hother : P.qz q other = true
    · rw [dif_pos hother]
      simp only [canonicalBasisWord, Pi.single_apply]
      split
      · rename_i heq
        exact (hne (congrArg Sigma.fst heq).symm).elim
      · rfl
    · rw [dif_neg hother]
      rfl
  · intro hnot
    exact (hnot (Finset.mem_univ z)).elim
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
    (S : OddScale) (q : P.Q) :
    tannerCoboundary1
        (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
        (map1Coord P A4 S (canonicalBasisWord q)) =
      map2Coord P A4 S
        (tannerCoboundary1 P (canonicalBasisWord q)) := by
  classical
  rw [map1Coord_canonicalBasis]
  have hroot : Pi.single
      (embedQRoot P S q (rzMap1QRoot P q S)) (1 : Field) =
      canonicalBasisWord (embedQRoot P S q (rzMap1QRoot P q S)) := by
    ext target
    simp [canonicalBasisWord, Pi.single_apply]
  have hrootMapped := congrArg
    (tannerCoboundary1
      (rzReplacementPresentation P A4.toTannerSquareAdmissible S)) hroot
  calc
    _ = (∑ z : P.Z, if hqz : P.qz q z = true then
          canonicalBasisWord
            ⟨z, qToZDoubleCylinderVertex P A4.toTannerSquareAdmissible
              q z hqz S (rzMap1QRoot P q S)⟩
        else 0) +
        ∑ z : P.Z, if hqz : P.qz q z = true then
          extendZVertexWord P S z
            (rzCzGraphBoundary P z S
              (rzMap1Connector P A4 q z hqz S))
        else 0 := by
      unfold map1BasisImage
      calc
        _ = tannerCoboundary1
              (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
              (Pi.single (embedQRoot P S q (rzMap1QRoot P q S)) 1) +
            tannerCoboundary1
              (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
              (∑ z : P.Z, if hqz : P.qz q z = true then
                extendZEdgeWord P S z
                  (rzMap1Connector P A4 q z hqz S) else 0) :=
          (tannerCoboundary1
            (rzReplacementPresentation P A4.toTannerSquareAdmissible S)).map_add
              _ _
        _ = _ := by
          calc
            _ = tannerCoboundary1
                  (rzReplacementPresentation P
                    A4.toTannerSquareAdmissible S)
                  (canonicalBasisWord
                    (embedQRoot P S q (rzMap1QRoot P q S))) +
                tannerCoboundary1
                  (rzReplacementPresentation P
                    A4.toTannerSquareAdmissible S)
                  (∑ z : P.Z, if hqz : P.qz q z = true then
                    extendZEdgeWord P S z
                      (rzMap1Connector P A4 q z hqz S) else 0) :=
              congrArg₂ (fun first second => first + second)
                hrootMapped rfl
            _ = _ := by
              rw [successor_delta1_qRoot, map_sum]
              apply congrArg (fun value => _ + value)
              apply Finset.sum_congr rfl
              intro z _
              by_cases hqz : P.qz q z = true
              · erw [dif_pos hqz, dif_pos hqz, rzCoboundary1_extendZEdgeWord]
              · erw [dif_neg hqz, dif_neg hqz, map_zero]
                rfl
    _ = (∑ z : P.Z, if hqz : P.qz q z = true then
          canonicalBasisWord
            ⟨z, qToZDoubleCylinderVertex P A4.toTannerSquareAdmissible
              q z hqz S (rzMap1QRoot P q S)⟩
        else 0) +
        ∑ z : P.Z, if hqz : P.qz q z = true then
          (canonicalBasisWord ⟨z, rzMap1ZRoot P A4 z S⟩ +
            canonicalBasisWord
              ⟨z, qToZDoubleCylinderVertex P A4.toTannerSquareAdmissible
                q z hqz S (rzMap1QRoot P q S)⟩)
        else 0 := by
      apply congrArg (fun value => _ + value)
      apply Finset.sum_congr rfl
      intro z _
      by_cases hqz : P.qz q z = true
      · rw [dif_pos hqz, dif_pos hqz,
          rzMap1Connector_delta1, extendZVertexWord_add,
          extendZVertexWord_canonicalBasis,
          extendZVertexWord_canonicalBasis]
      · rw [dif_neg hqz, dif_neg hqz]
    _ = ∑ z : P.Z, if hqz : P.qz q z = true then
          canonicalBasisWord ⟨z, rzMap1ZRoot P A4 z S⟩
        else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hqz : P.qz q z = true
      · rw [dif_pos hqz, dif_pos hqz, dif_pos hqz]
        let qWord : Word Field (RZZ P S) := canonicalBasisWord
          ⟨z, qToZDoubleCylinderVertex P A4.toTannerSquareAdmissible
            q z hqz S (rzMap1QRoot P q S)⟩
        let zWord : Word Field (RZZ P S) :=
          canonicalBasisWord ⟨z, rzMap1ZRoot P A4 z S⟩
        change qWord + (zWord + qWord) = zWord
        calc
          qWord + (zWord + qWord) = (qWord + qWord) + zWord := by
            ac_rfl
          _ = 0 + zWord := by rw [word_add_self]
          _ = zWord := zero_add zWord
      · rw [dif_neg hqz, dif_neg hqz, dif_neg hqz, zero_add]
    _ = _ := by
      rw [tannerCoboundary1_canonicalBasis_sum, map_sum]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hqz : P.qz q z = true
      · rw [dif_pos hqz, if_pos hqz, map2Coord_canonicalBasis]
      · rw [dif_neg hqz, if_neg hqz, map_zero]
end QEC.Coding.BDL26RZMap1CoordinateBridge

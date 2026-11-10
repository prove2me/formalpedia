-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementCochainMaps.subdivisionWholeFaceChain_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:04:38.569493+00:00
-- url     : https://prove2.me/submissions/fe27e50c-8a44-448c-921f-c241cfb0e13f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_subdivisionFaceBoundaryEdge_injective
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_subdivisionFaceEdgeMatrix_eq_one_iff
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzFace_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzQ_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzX_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzZ_card
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_map2Coord_canonicalBasis
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary0_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
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
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.map2Coord_canonicalBasis
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary0_canonicalBasis_apply
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1_canonicalBasis_apply
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
namespace QEC.Coding.BDL26ReplacementCochainMaps
open scoped BigOperators Classical
open QEC.Coding
open QEC.Coding.BDL26FiniteTannerSquare
open QEC.Coding.BDL26TannerLocalRegularity
open QEC.Coding.BDL26RXLocalReplacement
open QEC.Coding.BDL26RZLocalReplacement
open QEC.Coding.BDL26RZMap1CoordinateBridge
open QEC.Coding.MultiscaleDecoder
private theorem subdivisionBoundary2_canonicalBasis
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (i j : Fin S.half) :
    subdivisionBoundary2 P x S
        (canonicalBasisWord (⟨face, i, j⟩ : SubdivisionFace P x S)) =
      canonicalBasisWord
          (subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (0, 0)) +
        canonicalBasisWord
          (subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (1, 1)) +
        canonicalBasisWord
          (subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (0, 1)) +
      canonicalBasisWord
          (subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (1, 0)) := by
  classical
  ext edge
  unfold subdivisionBoundary2
  rw [Matrix.toLin'_apply]
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_single (⟨face, i, j⟩ : SubdivisionFace P x S)]
  · rw [show canonicalBasisWord (F := Field)
          (⟨face, i, j⟩ : SubdivisionFace P x S) ⟨face, i, j⟩ = 1 by
        simp [canonicalBasisWord, Pi.single_apply]]
    simp only [mul_one, Pi.add_apply]
    have hslot := subdivisionFaceBoundaryEdge_injective
        P x S (⟨face, i, j⟩ : SubdivisionFace P x S)
    have h00_11 :
        subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (0, 0) ≠
          subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (1, 1) :=
      Function.Injective.ne hslot (by decide)
    have h00_01 :
        subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (0, 0) ≠
          subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (0, 1) :=
      Function.Injective.ne hslot (by decide)
    have h00_10 :
        subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (0, 0) ≠
          subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (1, 0) :=
      Function.Injective.ne hslot (by decide)
    have h11_01 :
        subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (1, 1) ≠
          subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (0, 1) :=
      Function.Injective.ne hslot (by decide)
    have h11_10 :
        subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (1, 1) ≠
          subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (1, 0) :=
      Function.Injective.ne hslot (by decide)
    have h01_10 :
        subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (0, 1) ≠
          subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (1, 0) :=
      Function.Injective.ne hslot (by decide)
    have hbasis_self (a : SubdivisionEdge P x S) :
        canonicalBasisWord (F := Field) a a = 1 := by
      simp [canonicalBasisWord, Pi.single_apply]
    have hbasis_ne {a b : SubdivisionEdge P x S} (h : a ≠ b) :
        canonicalBasisWord (F := Field) a b = 0 := by
      simp [canonicalBasisWord, Pi.single_apply, h]
    by_cases h00 : edge =
        subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (0, 0)
    · have hmatrix : subdivisionFaceEdgeMatrix P x S edge ⟨face, i, j⟩ = 1 :=
        (subdivisionFaceEdgeMatrix_eq_one_iff P x S edge ⟨face, i, j⟩).2
          ⟨(0, 0), h00.symm⟩
      subst edge
      rw [hmatrix, hbasis_self, hbasis_ne h00_11.symm,
        hbasis_ne h00_01.symm, hbasis_ne h00_10.symm]
      simp
    · by_cases h11 : edge =
          subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (1, 1)
      · have hmatrix : subdivisionFaceEdgeMatrix P x S edge ⟨face, i, j⟩ = 1 :=
          (subdivisionFaceEdgeMatrix_eq_one_iff P x S edge ⟨face, i, j⟩).2
            ⟨(1, 1), h11.symm⟩
        subst edge
        rw [hmatrix, hbasis_ne h00_11, hbasis_self,
          hbasis_ne h11_01.symm, hbasis_ne h11_10.symm]
        simp
      · by_cases h01 : edge =
            subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (0, 1)
        · have hmatrix : subdivisionFaceEdgeMatrix P x S edge ⟨face, i, j⟩ = 1 :=
            (subdivisionFaceEdgeMatrix_eq_one_iff P x S edge ⟨face, i, j⟩).2
              ⟨(0, 1), h01.symm⟩
          subst edge
          rw [hmatrix, hbasis_ne h00_01, hbasis_ne h11_01,
            hbasis_self, hbasis_ne h01_10.symm]
          simp
        · by_cases h10 : edge =
              subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (1, 0)
          · have hmatrix : subdivisionFaceEdgeMatrix P x S edge ⟨face, i, j⟩ = 1 :=
              (subdivisionFaceEdgeMatrix_eq_one_iff P x S edge ⟨face, i, j⟩).2
                ⟨(1, 0), h10.symm⟩
            subst edge
            rw [hmatrix, hbasis_ne h00_10, hbasis_ne h11_10,
              hbasis_ne h01_10, hbasis_self]
            simp
          · have hmatrix_ne :
                subdivisionFaceEdgeMatrix P x S edge ⟨face, i, j⟩ ≠ 1 := by
              intro hmatrix
              obtain ⟨slot, hslot_eq⟩ :=
                (subdivisionFaceEdgeMatrix_eq_one_iff
                  P x S edge ⟨face, i, j⟩).1 hmatrix
              rcases slot with ⟨first, second⟩
              fin_cases first <;> fin_cases second
              · exact h00 hslot_eq.symm
              · exact h01 hslot_eq.symm
              · exact h10 hslot_eq.symm
              · exact h11 hslot_eq.symm
            have hmatrix_zero :
                subdivisionFaceEdgeMatrix P x S edge ⟨face, i, j⟩ = 0 := by
              generalize hvalue_eq :
                subdivisionFaceEdgeMatrix P x S edge ⟨face, i, j⟩ = hvalue
              fin_cases hvalue
              · rfl
              · exfalso
                apply hmatrix_ne
                exact hvalue_eq
            have hb00 : canonicalBasisWord (F := Field)
                (subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (0, 0)) edge = 0 :=
              hbasis_ne (Ne.symm h00)
            have hb11 : canonicalBasisWord (F := Field)
                (subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (1, 1)) edge = 0 :=
              hbasis_ne (Ne.symm h11)
            have hb01 : canonicalBasisWord (F := Field)
                (subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (0, 1)) edge = 0 :=
              hbasis_ne (Ne.symm h01)
            have hb10 : canonicalBasisWord (F := Field)
                (subdivisionFaceBoundaryEdge P x S ⟨face, i, j⟩ (1, 0)) edge = 0 :=
              hbasis_ne (Ne.symm h10)
            rw [hmatrix_zero, hb00, hb11, hb01, hb10]
            simp
  · intro other hne
    rw [show canonicalBasisWord (F := Field)
        (⟨face, i, j⟩ : SubdivisionFace P x S) other = 0 by
      simp [canonicalBasisWord, Pi.single_apply, Ne.symm hne]]
    simp
private theorem fin_sum_adjacent_cancel
    (n : Nat) (values : Fin (n + 1) → Field) :
    (∑ i : Fin n, (values i.castSucc + values i.succ)) =
      values 0 + values (Fin.last n) := by
  rw [Finset.sum_add_distrib]
  have hcast := Fin.sum_univ_castSucc values
  have hsucc := Fin.sum_univ_succ values
  have hself (value : Field) : value + value = 0 := by
    fin_cases value <;> rfl
  have hcast' : (∑ i : Fin n, values i.castSucc) =
      (∑ i : Fin (n + 1), values i) + values (Fin.last n) := by
    calc
      _ = (∑ i : Fin n, values i.castSucc) +
          (values (Fin.last n) + values (Fin.last n)) := by rw [hself, add_zero]
      _ = ((∑ i : Fin n, values i.castSucc) + values (Fin.last n)) +
          values (Fin.last n) := by module
      _ = _ := by rw [← hcast]
  have hsucc' : (∑ i : Fin n, values i.succ) =
      values 0 + ∑ i : Fin (n + 1), values i := by
    calc
      _ = (values 0 + values 0) + (∑ i : Fin n, values i.succ) := by
        rw [hself, zero_add]
      _ = values 0 + (values 0 + ∑ i : Fin n, values i.succ) := by module
      _ = _ := by rw [← hsucc]
  rw [hcast', hsucc']
  calc
    _ = ((∑ i : Fin (n + 1), values i) +
          ∑ i : Fin (n + 1), values i) +
        (values (Fin.last n) + values 0) := by module
    _ = values (Fin.last n) + values 0 := by rw [hself, zero_add]
    _ = _ := add_comm _ _
private theorem fin_sum_adjacent_cancel_word
    {Index : Type} (n : Nat) (values : Fin (n + 1) → Word Field Index) :
    (∑ i : Fin n, (values i.castSucc + values i.succ)) =
      values 0 + values (Fin.last n) := by
  ext coordinate
  simp only [Finset.sum_apply, Pi.add_apply]
  exact fin_sum_adjacent_cancel n (fun i => values i coordinate)
private theorem subdivisionHorizontalRows_cancel
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) :
    (∑ i : Fin S.half, ∑ j : Fin S.half,
        canonicalBasisWord (F := Field)
          (subdivisionHorizontalEdge P x S face i j.castSucc)) +
      (∑ i : Fin S.half, ∑ j : Fin S.half,
        canonicalBasisWord (F := Field)
          (subdivisionHorizontalEdge P x S face i j.succ)) =
      (∑ i : Fin S.half,
        canonicalBasisWord (F := Field)
          (subdivisionHorizontalEdge P x S face i 0)) +
      (∑ i : Fin S.half,
        canonicalBasisWord (F := Field)
          (subdivisionHorizontalEdge P x S face i (Fin.last S.half))) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  exact fin_sum_adjacent_cancel_word S.half
    (fun j => canonicalBasisWord (F := Field)
      (subdivisionHorizontalEdge P x S face i j))
private theorem subdivisionVerticalColumns_cancel
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) :
    (∑ i : Fin S.half, ∑ j : Fin S.half,
        canonicalBasisWord (F := Field)
          (subdivisionVerticalEdge P x S face i.succ j)) +
      (∑ i : Fin S.half, ∑ j : Fin S.half,
        canonicalBasisWord (F := Field)
          (subdivisionVerticalEdge P x S face i.castSucc j)) =
      (∑ j : Fin S.half,
        canonicalBasisWord (F := Field)
          (subdivisionVerticalEdge P x S face 0 j)) +
      (∑ j : Fin S.half,
        canonicalBasisWord (F := Field)
          (subdivisionVerticalEdge P x S face (Fin.last S.half) j)) := by
  calc
    _ = (∑ j : Fin S.half, ∑ i : Fin S.half,
          canonicalBasisWord (F := Field)
            (subdivisionVerticalEdge P x S face i.succ j)) +
        (∑ j : Fin S.half, ∑ i : Fin S.half,
          canonicalBasisWord (F := Field)
            (subdivisionVerticalEdge P x S face i.castSucc j)) := by
      congr 1 <;> exact Finset.sum_comm
    _ = ∑ j : Fin S.half,
        ((∑ i : Fin S.half, canonicalBasisWord (F := Field)
            (subdivisionVerticalEdge P x S face i.succ j)) +
          (∑ i : Fin S.half, canonicalBasisWord (F := Field)
            (subdivisionVerticalEdge P x S face i.castSucc j))) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ j : Fin S.half,
        (canonicalBasisWord (F := Field)
            (subdivisionVerticalEdge P x S face 0 j) +
          canonicalBasisWord (F := Field)
            (subdivisionVerticalEdge P x S face (Fin.last S.half) j)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_add_distrib]
      calc
        _ = ∑ i : Fin S.half,
            (canonicalBasisWord (F := Field)
                (subdivisionVerticalEdge P x S face i.castSucc j) +
              canonicalBasisWord (F := Field)
                (subdivisionVerticalEdge P x S face i.succ j)) := by
          apply Finset.sum_congr rfl
          intro i _
          exact add_comm _ _
        _ = _ := fin_sum_adjacent_cancel_word S.half
          (fun i => canonicalBasisWord (F := Field)
            (subdivisionVerticalEdge P x S face i j))
    _ = _ := by rw [Finset.sum_add_distrib]
end QEC.Coding.BDL26ReplacementCochainMaps
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementCochainMaps
open scoped BigOperators Classical
open QEC.Coding
open QEC.Coding.BDL26FiniteTannerSquare
open QEC.Coding.BDL26TannerLocalRegularity
open QEC.Coding.BDL26RXLocalReplacement
open QEC.Coding.BDL26RZLocalReplacement
open QEC.Coding.BDL26RZMap1CoordinateBridge
open QEC.Coding.MultiscaleDecoder
namespace QEC.Coding.BDL26ReplacementCochainMaps
theorem _root_.solution
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) :
    subdivisionBoundary2 P x S (subdivisionWholeFaceChain P x S face) =
      (∑ i : Fin S.half,
          canonicalBasisWord
            (subdivisionHorizontalEdge P x S face i (rzGridZero S))) +
        (∑ i : Fin S.half,
          canonicalBasisWord
            (subdivisionHorizontalEdge P x S face i (rzGridLast S))) +
        (∑ j : Fin S.half,
          canonicalBasisWord
            (subdivisionVerticalEdge P x S face (rzGridZero S) j)) +
      (∑ j : Fin S.half,
        canonicalBasisWord
          (subdivisionVerticalEdge P x S face (rzGridLast S) j)) := by
  classical
  unfold subdivisionWholeFaceChain
  simp_rw [map_sum, subdivisionBoundary2_canonicalBasis,
    subdivisionFaceBoundaryEdge_zero_zero,
    subdivisionFaceBoundaryEdge_zero_one,
    subdivisionFaceBoundaryEdge_one_zero,
    subdivisionFaceBoundaryEdge_one_one]
  simp_rw [Finset.sum_add_distrib]
  let horizontalLow : Word Field (SubdivisionEdge P x S) :=
    ∑ i : Fin S.half, ∑ j : Fin S.half,
      canonicalBasisWord
        (subdivisionHorizontalEdge P x S face i j.castSucc)
  let horizontalHigh : Word Field (SubdivisionEdge P x S) :=
    ∑ i : Fin S.half, ∑ j : Fin S.half,
      canonicalBasisWord
        (subdivisionHorizontalEdge P x S face i j.succ)
  let verticalHigh : Word Field (SubdivisionEdge P x S) :=
    ∑ i : Fin S.half, ∑ j : Fin S.half,
      canonicalBasisWord
        (subdivisionVerticalEdge P x S face i.succ j)
  let verticalLow : Word Field (SubdivisionEdge P x S) :=
    ∑ i : Fin S.half, ∑ j : Fin S.half,
      canonicalBasisWord
        (subdivisionVerticalEdge P x S face i.castSucc j)
  change horizontalLow + verticalHigh + horizontalHigh + verticalLow = _
  have hhorizontal : horizontalLow + horizontalHigh =
      (∑ i : Fin S.half, canonicalBasisWord
        (subdivisionHorizontalEdge P x S face i 0)) +
      (∑ i : Fin S.half, canonicalBasisWord
        (subdivisionHorizontalEdge P x S face i (Fin.last S.half))) := by
    simpa only [horizontalLow, horizontalHigh] using
      subdivisionHorizontalRows_cancel P x S face
  have hvertical : verticalHigh + verticalLow =
      (∑ j : Fin S.half, canonicalBasisWord
        (subdivisionVerticalEdge P x S face 0 j)) +
      (∑ j : Fin S.half, canonicalBasisWord
        (subdivisionVerticalEdge P x S face (Fin.last S.half) j)) := by
    simpa only [verticalHigh, verticalLow] using
      subdivisionVerticalColumns_cancel P x S face
  have hzero : (0 : Fin (S.half + 1)) = rzGridZero S := by
    apply Fin.ext
    rfl
  have hlast : Fin.last S.half = rzGridLast S := by
    apply Fin.ext
    rfl
  calc
    _ = (horizontalLow + horizontalHigh) + (verticalHigh + verticalLow) := by
      module
    _ =
        (((∑ i : Fin S.half, canonicalBasisWord
            (subdivisionHorizontalEdge P x S face i 0)) +
          (∑ i : Fin S.half, canonicalBasisWord
            (subdivisionHorizontalEdge P x S face i (Fin.last S.half)))) +
        ((∑ j : Fin S.half, canonicalBasisWord
            (subdivisionVerticalEdge P x S face 0 j)) +
          (∑ j : Fin S.half, canonicalBasisWord
            (subdivisionVerticalEdge P x S face (Fin.last S.half) j)))) := by
      rw [hhorizontal, hvertical]
    _ = _ := by
      rw [hzero, hlast]
      module
end QEC.Coding.BDL26ReplacementCochainMaps

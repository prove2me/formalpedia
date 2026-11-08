-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData.rx_coarse_graining_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:14:43.906675+00:00
-- url     : https://prove2.me/submissions/8af6b5d9-00a5-4169-bfc1-8adffd891848

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_xSector_mem_of_region
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_qSector_mem_of_region
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_zero_outside_sector_of_zero_x_zero_q
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_cqRepresentative_difference_exists
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_hammingWeight_map2_eq_double
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_cx_cleaning_explicit
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_cq_cleaning_explicit
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_cqCorrectionRG_supported
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_selectedMap_eq_rx_of_odd_input
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_coarseProjection_eq_of_map2
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_cxCorrectionTotal_eq_explicit
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_cqCorrectionTotal_eq_explicit
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_BDL26CochainFamily_coboundary1_comp_coboundary0
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXConstructionContractSlice_cq_local_ranges_of_error
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXConstructionContractSlice_cx_error_cleaning_all
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXConstructionContractSlice_cx_local_ranges_of_syndrome
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_extend_restrict_sum_eq_mask
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
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
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



set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open QEC.Coding.MultiscaleDecoder.RXCoarseGraining
open scoped BigOperators
universe u v
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {i : StepIndex depth}
open QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
variable {X Q Z : Type v} [Fintype X] [DecidableEq X]
  [Fintype Q] [DecidableEq Q] [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
variable (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
  (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz)
namespace QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
theorem _root_.solution
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (hOdd : i.succ.val % 2 = 1)
    (sigma : D.family.Syndrome i.succ) :
    ∃ sigma' : D.family.Syndrome i.castSucc,
      ∃ correction : D.family.Correction i.succ,
        (sigma' : D.family.Cochain2 i.castSucc) =
            rxCoarseWord A (sigma : D.family.Cochain2 i.succ) ∧
        correction = rxCorrectionTotal A (sigma : D.family.Cochain2 i.succ) ∧
        (sigma : D.family.Cochain2 i.succ) =
            D.family.coboundary1 i.succ correction +
              (D.selectedMap i).map2 sigma' ∧
        2 * HammingWeight (sigma' : D.family.Cochain2 i.castSucc) ≤
          HammingWeight (sigma : D.family.Cochain2 i.succ) ∧
        HammingWeight (sigma' : D.family.Cochain2 i.castSucc) ≤
          HammingWeight (sigma : D.family.Cochain2 i.succ) / 2 ∧
        SupportedOn A.zSector ((D.selectedMap i).map2 sigma') ∧
        (∀ p ∈ A.xSector, ((D.selectedMap i).map2 sigma') p = 0) ∧
        (∀ p ∈ A.qSector, ((D.selectedMap i).map2 sigma') p = 0) := by
  classical
  let hCxLocal := A.contract.cx_local_ranges_of_syndrome sigma
  let cxCorrection := cxCorrectionRG A sigma.1 hCxLocal
  let sigma₁ := sigma.1 + D.family.coboundary1 i.succ cxCorrection
  have hCx := cx_cleaning_explicit A sigma
  have hSigma₁Weight : HammingWeight sigma₁ ≤ HammingWeight sigma.1 := by
    simpa [sigma₁, cxCorrection] using hCx.1
  have hSigma₁X : ∀ p ∈ A.xSector, sigma₁ p = 0 := by
    simpa [sigma₁, cxCorrection] using hCx.2
  obtain ⟨error, hError⟩ := sigma.property
  let error₁ := error + cxCorrection
  have hError₁ : D.family.coboundary1 i.succ error₁ = sigma₁ := by
    dsimp [error₁, sigma₁]
    rw [map_add, hError]
  have hCxCocycle : ∀ x,
      A.contract.rx_local_complexes.cxDelta1 x
        (restrictWordLinear (Lx.correctionRegion x) error₁) = 0 := by
    intro x
    have hz : restrictWordLinear (Lx.syndromeRegion x)
        (D.family.coboundary1 i.succ error₁) = 0 := by
      funext j
      have hj : (j : C2 i.succ) ∈ A.xSector := by
        apply xSector_mem_of_region A
        exact Finset.mem_biUnion.2 ⟨x, Finset.mem_univ _, j.property⟩
      change D.family.coboundary1 i.succ error₁ j.1 = 0
      rw [hError₁]
      exact hSigma₁X j.1 hj
    rw [← A.contract.support_decomposition.cxDelta1_restriction_global x error₁]
    exact hz
  obtain ⟨stabilizers, hStabilizers⟩ :=
    A.contract.cx_error_cleaning_all error₁ hCxCocycle
  let stabilizerCorrection : D.family.Correction i.succ :=
    D.family.coboundary0 i.succ
      (∑ x : X, A.contract.support_decomposition.cxLift0 x (stabilizers x))
  have hStabilizerZero : D.family.coboundary1 i.succ stabilizerCorrection = 0 := by
    dsimp [stabilizerCorrection]
    have hcomp := BDL26CochainFamily.coboundary1_comp_coboundary0
      D.family i.succ
    have hcomp' := LinearMap.congr_fun hcomp
      (∑ x : X, A.contract.support_decomposition.cxLift0 x (stabilizers x))
    simpa [LinearMap.comp_apply] using hcomp'
  let error₂ := error₁ + stabilizerCorrection
  have hError₂X : ∀ p ∈ correctionRegionUnion Lx, error₂ p = 0 := by
    intro p hp
    rcases Finset.mem_biUnion.1 hp with ⟨x, hx, hpx⟩
    have hlocal := hStabilizers x
    have hlocal' := congrFun hlocal ⟨p, hpx⟩
    exact hlocal'
  have hError₂ : D.family.coboundary1 i.succ error₂ = sigma₁ := by
    dsimp [error₂, stabilizerCorrection]
    rw [map_add]
    rw [hStabilizerZero, add_zero, hError₁]
  have hError₂Supported : SupportedOn A.qCorrectionSector error₂ := by
    intro p hp
    have hcover : p ∈ correctionRegionUnion Lx ∪ A.qCorrectionSector := by
      rw [A.correction_sectors_cover]
      exact Finset.mem_univ p
    have hpX : p ∈ correctionRegionUnion Lx := by
      rcases (by simpa only [Finset.mem_union] using hcover) with hpX | hpQ
      · exact hpX
      · exact (hp hpQ).elim
    exact hError₂X p hpX
  have hError₂XRestrictions : ∀ x,
      restrictWordLinear (Lx.correctionRegion x) error₂ = 0 := by
    intro x
    funext p
    exact hError₂X p.1 (Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _, p.2⟩)
  let hCqLocalRaw := A.contract.cq_local_ranges_of_error error₂ hError₂XRestrictions
  have hCqLocal : ∀ q, restrictWordLinear (Lq.syndromeRegion q) sigma₁ ∈
      LinearMap.range (A.contract.rx_local_complexes.cqDelta1 q) := by
    intro q
    rw [← hError₂]
    exact hCqLocalRaw q
  let cqCorrection := cqCorrectionRG A sigma₁ hCqLocal
  let sigma₂ := sigma₁ + D.family.coboundary1 i.succ cqCorrection
  have hCq := cq_cleaning_explicit A sigma₁ hCqLocal hSigma₁X
  have hSigma₂Weight : HammingWeight sigma₂ ≤ HammingWeight sigma₁ := by
    simpa [sigma₂, cqCorrection] using hCq.1
  have hSigma₂X : ∀ p ∈ A.xSector, sigma₂ p = 0 := by
    simpa [sigma₂, cqCorrection] using hCq.2.2
  have hSigma₂Q : ∀ p ∈ A.qSector, sigma₂ p = 0 := by
    simpa [sigma₂, cqCorrection] using hCq.2.1
  let error₃ := error₂ + cqCorrection
  have hError₃ : D.family.coboundary1 i.succ error₃ = sigma₂ := by
    dsimp [error₃, sigma₂]
    rw [map_add, hError₂]
  have hError₃Supported : SupportedOn A.qCorrectionSector error₃ := by
    intro p hp
    change error₂ p + cqCorrectionRG A sigma₁ hCqLocal p = 0
    rw [hError₂Supported p hp,
      cqCorrectionRG_supported A sigma₁ hCqLocal p hp, zero_add]
  have hError₃XRestrictions : ∀ x,
      restrictWordLinear (Lx.correctionRegion x) error₃ = 0 := by
    intro x
    funext p
    apply hError₃Supported p.1
    intro hpQ
    exact Finset.disjoint_left.mp A.correction_sectors_disjoint
      (Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _, p.2⟩) hpQ
  have hError₃CqCocycle : ∀ q,
      A.contract.rx_local_complexes.cqDelta1 q
        (restrictWordLinear (Lq.correctionRegion q) error₃) = 0 := by
    intro q
    have hz : restrictWordLinear (Lq.syndromeRegion q)
        (D.family.coboundary1 i.succ error₃) = 0 := by
      funext j
      have hj : (j : C2 i.succ) ∈ A.qSector := by
        apply qSector_mem_of_region A
        exact Finset.mem_biUnion.2 ⟨q, Finset.mem_univ _, j.property⟩
      change D.family.coboundary1 i.succ error₃ j.1 = 0
      rw [hError₃]
      exact hSigma₂Q j.1 hj
    rw [← A.contract.support_decomposition.cqDelta1_restriction_global q error₃ hError₃XRestrictions]
    exact hz
  have hError₃SupportedOnRegions :
      SupportedOn (correctionRegionUnion Lq) error₃ := by
    intro p hp
    apply hError₃Supported p
    simpa [A.qCorrectionSector_eq_regions] using hp
  have hError₃Decomposition :
      error₃ = ∑ q : Q, extendWordLinear (Lq.correctionRegion q)
        (restrictWordLinear (Lq.correctionRegion q) error₃) := by
    rw [extend_restrict_sum_eq_mask
      (fun q => Lq.correctionRegion q)
      A.cq_correction_regions_pairwise_disjoint error₃]
    funext p
    by_cases hp : p ∈ correctionRegionUnion Lq
    · change error₃ p = if p ∈ correctionRegionUnion Lq then error₃ p else 0
      rw [if_pos hp]
    · change error₃ p = if p ∈ correctionRegionUnion Lq then error₃ p else 0
      rw [if_neg hp]
      exact hError₃SupportedOnRegions p hp
  let qClasses := qCohomologyClass A error₃ hError₃CqCocycle
  have hRepresentativeDifference : ∀ q, ∃ s : Word Field (Q0 q),
      A.contract.rx_local_complexes.cqDelta0 q s =
        (A.cqRepresentative q (qClasses q)).1 -
          restrictWordLinear (Lq.correctionRegion q) error₃ := by
    intro q
    exact cqRepresentative_difference_exists A error₃ hError₃CqCocycle q
  let cqStabilizers : ∀ q, Word Field (Q0 q) :=
    fun q => Classical.choose (hRepresentativeDifference q)
  have hCqStabilizers : ∀ q,
      A.contract.rx_local_complexes.cqDelta0 q (cqStabilizers q) =
        (A.cqRepresentative q (qClasses q)).1 -
          restrictWordLinear (Lq.correctionRegion q) error₃ := by
    intro q
    exact Classical.choose_spec (hRepresentativeDifference q)
  let lowerCorrection := A.qCohomologyEquiv qClasses
  let qStabilizerCorrection : D.family.Correction i.succ :=
    D.family.coboundary0 i.succ
      (∑ q : Q, A.contract.support_decomposition.cqLift0 q
        (cqStabilizers q))
  let error₄ := error₃ + qStabilizerCorrection
  have hQStabilizerZero :
      D.family.coboundary1 i.succ qStabilizerCorrection = 0 := by
    dsimp [qStabilizerCorrection]
    have hcomp := BDL26CochainFamily.coboundary1_comp_coboundary0
      D.family i.succ
    have hcomp' := LinearMap.congr_fun hcomp
      (∑ q : Q, A.contract.support_decomposition.cqLift0 q
        (cqStabilizers q))
    simpa [LinearMap.comp_apply] using hcomp'
  have hError₄ : D.family.coboundary1 i.succ error₄ = sigma₂ := by
    dsimp [error₄]
    rw [map_add, hQStabilizerZero, add_zero, hError₃]
  have hRepresentativeSum :
      (∑ q : Q, extendWordLinear (Lq.correctionRegion q)
        ((A.cqRepresentative q (qClasses q)).1)) = error₄ := by
    calc
      (∑ q : Q, extendWordLinear (Lq.correctionRegion q)
          ((A.cqRepresentative q (qClasses q)).1)) =
        ∑ q : Q, (extendWordLinear (Lq.correctionRegion q)
          (restrictWordLinear (Lq.correctionRegion q) error₃) +
          extendWordLinear (Lq.correctionRegion q)
            (A.contract.rx_local_complexes.cqDelta0 q
              (cqStabilizers q))) := by
            apply Finset.sum_congr rfl
            intro q hq
            have hqdiff := hCqStabilizers q
            have hqrep :
                (A.cqRepresentative q (qClasses q)).1 =
                  restrictWordLinear (Lq.correctionRegion q) error₃ +
                    A.contract.rx_local_complexes.cqDelta0 q
                      (cqStabilizers q) := by
              have hrr :
                  restrictWordLinear (Lq.correctionRegion q) error₃ +
                      restrictWordLinear (Lq.correctionRegion q) error₃ =
                    (0 : Word Field (LocalRegionIndex (Lq.correctionRegion q))) := by
                ext p
                exact ZModModule.add_self _
              calc
                (A.cqRepresentative q (qClasses q)).1 =
                    ((A.cqRepresentative q (qClasses q)).1 +
                      restrictWordLinear (Lq.correctionRegion q) error₃) +
                      restrictWordLinear (Lq.correctionRegion q) error₃ := by
                        symm
                        rw [add_assoc, hrr, add_zero]
                _ = A.contract.rx_local_complexes.cqDelta0 q
                      (cqStabilizers q) +
                      restrictWordLinear (Lq.correctionRegion q) error₃ := by
                        rw [hqdiff, ZModModule.sub_eq_add,
                          add_assoc, hrr, add_zero]
                _ = restrictWordLinear (Lq.correctionRegion q) error₃ +
                      A.contract.rx_local_complexes.cqDelta0 q
                        (cqStabilizers q) := by abel
            rw [hqrep, map_add]
      _ = (∑ q : Q, extendWordLinear (Lq.correctionRegion q)
            (restrictWordLinear (Lq.correctionRegion q) error₃)) +
          (∑ q : Q, extendWordLinear (Lq.correctionRegion q)
            (A.contract.rx_local_complexes.cqDelta0 q
              (cqStabilizers q))) := by
            rw [Finset.sum_add_distrib]
      _ = error₃ + D.family.coboundary0 i.succ
          (∑ q : Q, A.contract.support_decomposition.cqLift0 q
            (cqStabilizers q)) := by
            rw [← hError₃Decomposition]
            rw [← A.cqDelta0_sum_decomposition]
      _ = error₄ := by rfl
  have hMap1 : (D.rxMap i).map1 lowerCorrection = error₄ := by
    rw [A.rxMap1_eq_cqRepresentative lowerCorrection]
    simpa [lowerCorrection] using hRepresentativeSum
  let lowerSyndrome : D.family.Syndrome i.castSucc :=
    ⟨D.family.coboundary1 i.castSucc lowerCorrection, by
      exact ⟨lowerCorrection, rfl⟩⟩
  have hMap2 : (D.rxMap i).map2 lowerSyndrome = sigma₂ := by
    have hcomm := LinearMap.congr_fun (D.rxMap i).commutes_coboundary1 lowerCorrection
    simp only [LinearMap.comp_apply] at hcomm
    rw [hMap1] at hcomm
    rw [hError₄] at hcomm
    exact hcomm.symm
  have hSelected := selectedMap_eq_rx_of_odd_input D i hOdd
  have hMap2Selected : (D.selectedMap i).map2 lowerSyndrome = sigma₂ := by
    rw [hSelected]
    exact hMap2
  have hCoarseProjection : coarseProjection A sigma₂ =
      (lowerSyndrome : D.family.Cochain2 i.castSucc) :=
    coarseProjection_eq_of_map2 A sigma₂
      (lowerSyndrome : D.family.Cochain2 i.castSucc) hMap2
  let coarseRange : coarseProjection A sigma₂ ∈
      LinearMap.range (D.family.coboundary1 i.castSucc) := by
    rw [hCoarseProjection]
    exact lowerSyndrome.property
  let coarseSyndrome : D.family.Syndrome i.castSucc :=
    ⟨coarseProjection A sigma₂, coarseRange⟩
  have hSyndromeEq : coarseSyndrome = lowerSyndrome := by
    apply Subtype.ext
    exact hCoarseProjection
  have hMap2Coarse : (D.selectedMap i).map2 coarseSyndrome = sigma₂ := by
    rw [hSelected]
    rw [hSyndromeEq]
    exact hMap2
  have hCxTotal : cxCorrectionTotal A sigma.1 = cxCorrection := by
    simpa [cxCorrection] using
      (cxCorrectionTotal_eq_explicit A sigma.1 hCxLocal)
  have hSigmaAfterCx : rxSigmaAfterCx A sigma.1 = sigma₁ := by
    simp [rxSigmaAfterCx, hCxTotal, sigma₁]
  have hCqLocalTotal : CqLocalRange A sigma.1 := by
    intro q
    change restrictWordLinear (Lq.syndromeRegion q)
      (rxSigmaAfterCx A sigma.1) ∈
      LinearMap.range (A.contract.rx_local_complexes.cqDelta1 q)
    rw [hSigmaAfterCx]
    exact hCqLocal q
  have hCqTotal : cqCorrectionTotal A sigma.1 = cqCorrection := by
    have h := cqCorrectionTotal_eq_explicit A sigma.1 hCqLocalTotal
    calc
      cqCorrectionTotal A sigma.1 =
          cqCorrectionRG A (rxSigmaAfterCx A sigma.1) hCqLocalTotal := h
      _ = cqCorrection := by
        dsimp [cqCorrection]
        congr 1
  have hSigmaAfterCq : rxSigmaAfterCq A sigma.1 = sigma₂ := by
    simp [rxSigmaAfterCq, hSigmaAfterCx, hCqTotal, sigma₂]
  have hCoarseWord : rxCoarseWord A sigma.1 =
      (coarseSyndrome : D.family.Cochain2 i.castSucc) := by
    rw [rxCoarseWord, hSigmaAfterCq, hCoarseProjection]
    exact congrArg Subtype.val hSyndromeEq.symm
  have hSigma₂WeightFinal : HammingWeight sigma₂ ≤ HammingWeight sigma.1 :=
    hSigma₂Weight.trans hSigma₁Weight
  have hDouble : 2 * HammingWeight
        (lowerSyndrome : D.family.Cochain2 i.castSucc) ≤
      HammingWeight sigma.1 := by
    calc
      2 * HammingWeight (lowerSyndrome : D.family.Cochain2 i.castSucc) =
          HammingWeight ((D.rxMap i).map2 lowerSyndrome) := by
            symm
            exact hammingWeight_map2_eq_double A lowerSyndrome
      _ = HammingWeight sigma₂ := by rw [hMap2]
      _ ≤ HammingWeight sigma.1 := hSigma₂WeightFinal
  have hHalf : HammingWeight
        (lowerSyndrome : D.family.Cochain2 i.castSucc) ≤
      HammingWeight sigma.1 / 2 := by omega
  have hSupportZ : SupportedOn A.zSector sigma₂ :=
    RXCoarseGrainingData.zero_outside_sector_of_zero_x_zero_q A hSigma₂X hSigma₂Q
  let correction : D.family.Correction i.succ :=
    cxCorrection + cqCorrection
  have hCorrectionTotal : rxCorrectionTotal A sigma.1 = correction := by
    simp [rxCorrectionTotal, correction, hCxTotal, hCqTotal]
  have hDoubleCoarse : 2 * HammingWeight
        (coarseSyndrome : D.family.Cochain2 i.castSucc) ≤
      HammingWeight sigma.1 := by
    simpa [coarseSyndrome, hCoarseProjection] using hDouble
  have hHalfCoarse : HammingWeight
        (coarseSyndrome : D.family.Cochain2 i.castSucc) ≤
      HammingWeight sigma.1 / 2 := by
    simpa [coarseSyndrome, hCoarseProjection] using hHalf
  refine ⟨coarseSyndrome, correction, ?_, ?_, ?_, hDoubleCoarse, hHalfCoarse, ?_, ?_, ?_⟩
  · exact hCoarseWord.symm
  · exact hCorrectionTotal.symm
  · have hRel : sigma.1 =
        D.family.coboundary1 i.succ correction + sigma₂ := by
      dsimp [correction]
      rw [map_add]
      rw [← hError₃]
      dsimp [error₃, error₂, error₁]
      rw [map_add, map_add, map_add, hError, hStabilizerZero]
      abel
      simp [two_smul, ZModModule.add_self]
    rw [hMap2Coarse]
    exact hRel
  · rw [hMap2Coarse]
    exact hSupportZ
  · rw [hMap2Coarse]
    exact hSigma₂X
  · rw [hMap2Coarse]
    exact hSigma₂Q
end QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData

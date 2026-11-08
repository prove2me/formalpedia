-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXErrorTransport.q_sector_error_difference_transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:56:54.236198+00:00
-- url     : https://prove2.me/submissions/0cc027b6-61ae-407a-a94f-17ce911b7c8f

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXErrorTransport
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXErrorTransport_q_sector_transport
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_selectedMap_eq_rx_of_odd_input
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
variable {X Q Z : Type v} [Fintype X] [DecidableEq X]
  [Fintype Q] [DecidableEq Q] [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
open QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXErrorTransport
namespace QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXErrorTransport
theorem _root_.solution
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (hOdd : i.succ.val % 2 = 1)
    (left right : RXQSectorRun A)
    (hLeftSupported : SupportedOn A.qCorrectionSector left.upperCorrection)
    (hRightSupported : SupportedOn A.qCorrectionSector right.upperCorrection)
    (hLeftCocycle : ∀ q,
      A.contract.rx_local_complexes.cqDelta1 q
        (restrictWordLinear (Lq.correctionRegion q) left.upperCorrection) = 0)
    (hRightCocycle : ∀ q,
      A.contract.rx_local_complexes.cqDelta1 q
        (restrictWordLinear (Lq.correctionRegion q) right.upperCorrection) = 0)
    (eDelta : D.family.Cochain1 i.succ)
    (hDifference : eDelta = left.upperCorrection + right.upperCorrection) :
    ∃ eDeltaLower : D.family.Cochain1 i.castSucc,
      ∃ eDeltaSyndrome : D.family.Syndrome i.castSucc,
        ∃ eDeltaStabilizer : D.family.Cochain0 i.succ,
          (D.rxMap i).map1 eDeltaLower =
              eDelta + D.family.coboundary0 i.succ eDeltaStabilizer ∧
          D.family.coboundary1 i.succ
              (D.family.coboundary0 i.succ eDeltaStabilizer) = 0 ∧
          (eDeltaSyndrome : D.family.Cochain2 i.castSucc) =
              D.family.coboundary1 i.castSucc eDeltaLower ∧
          D.family.coboundary1 i.succ eDelta =
              (left.upperSyndrome : D.family.Cochain2 i.succ) +
                (right.upperSyndrome : D.family.Cochain2 i.succ) ∧
          (D.selectedMap i).map2 eDeltaSyndrome =
              D.family.coboundary1 i.succ eDelta ∧
          SupportedOn A.zSector ((D.selectedMap i).map2 eDeltaSyndrome) := by
  classical
  obtain ⟨leftLower, leftSyndrome, leftStabilizer,
      hLeftMap1, hLeftStabilizerZero, hLeftLowerSyndrome,
      hLeftMap2, hLeftSupport⟩ :=
    q_sector_transport A hOdd left.upperCorrection
      hLeftSupported hLeftCocycle
  obtain ⟨rightLower, rightSyndrome, rightStabilizer,
      hRightMap1, hRightStabilizerZero, hRightLowerSyndrome,
      hRightMap2, hRightSupport⟩ :=
    q_sector_transport A hOdd right.upperCorrection
      hRightSupported hRightCocycle
  let eDeltaLower := leftLower + rightLower
  let eDeltaStabilizer := leftStabilizer + rightStabilizer
  let eDeltaSyndrome : D.family.Syndrome i.castSucc :=
    ⟨D.family.coboundary1 i.castSucc eDeltaLower, by
      exact ⟨eDeltaLower, rfl⟩⟩
  have hMap1 : (D.rxMap i).map1 eDeltaLower =
      eDelta + D.family.coboundary0 i.succ eDeltaStabilizer := by
    calc
      (D.rxMap i).map1 eDeltaLower =
          (D.rxMap i).map1 leftLower + (D.rxMap i).map1 rightLower := by
            simp [eDeltaLower]
      _ = (left.upperCorrection + D.family.coboundary0 i.succ leftStabilizer) +
          (right.upperCorrection + D.family.coboundary0 i.succ rightStabilizer) := by
            rw [hLeftMap1, hRightMap1]
      _ = (left.upperCorrection + right.upperCorrection) +
          (D.family.coboundary0 i.succ leftStabilizer +
            D.family.coboundary0 i.succ rightStabilizer) := by abel
      _ = eDelta + D.family.coboundary0 i.succ eDeltaStabilizer := by
            rw [hDifference, ← map_add]
  have hStabilizerZero : D.family.coboundary1 i.succ
      (D.family.coboundary0 i.succ eDeltaStabilizer) = 0 := by
    calc
      D.family.coboundary1 i.succ
          (D.family.coboundary0 i.succ eDeltaStabilizer) =
          D.family.coboundary1 i.succ
            (D.family.coboundary0 i.succ leftStabilizer) +
          D.family.coboundary1 i.succ
            (D.family.coboundary0 i.succ rightStabilizer) := by
              simp [eDeltaStabilizer, map_add]
      _ = 0 := by rw [hLeftStabilizerZero, hRightStabilizerZero, add_zero]
  have hUpperSyndromeDifference :
      D.family.coboundary1 i.succ eDelta =
        (left.upperSyndrome : D.family.Cochain2 i.succ) +
          (right.upperSyndrome : D.family.Cochain2 i.succ) := by
    rw [hDifference, map_add, left.upperSyndrome_eq,
      right.upperSyndrome_eq]
  have hSelected : D.selectedMap i = D.rxMap i :=
    RXCoarseGrainingData.selectedMap_eq_rx_of_odd_input D i hOdd
  have hMap2 : (D.selectedMap i).map2 eDeltaSyndrome =
      D.family.coboundary1 i.succ eDelta := by
    have hcomm := LinearMap.congr_fun (D.rxMap i).commutes_coboundary1
      eDeltaLower
    simp only [LinearMap.comp_apply] at hcomm
    rw [hMap1, map_add, hStabilizerZero, add_zero] at hcomm
    simpa [eDeltaSyndrome, hSelected] using hcomm.symm
  have hSupport : SupportedOn A.zSector
      (D.family.coboundary1 i.succ eDelta) := by
    intro p hp
    rw [hDifference, map_add]
    rw [hLeftMap2] at hLeftSupport
    rw [hRightMap2] at hRightSupport
    simp only [Pi.add_apply]
    rw [hLeftSupport p hp, hRightSupport p hp, add_zero]
  refine ⟨eDeltaLower, eDeltaSyndrome, eDeltaStabilizer, hMap1,
    hStabilizerZero, ?_, hUpperSyndromeDifference, hMap2, ?_⟩
  · rfl
  · simpa [hMap2] using hSupport
end QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXErrorTransport

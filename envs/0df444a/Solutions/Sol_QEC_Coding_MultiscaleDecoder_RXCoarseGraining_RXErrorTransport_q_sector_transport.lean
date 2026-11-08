-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXErrorTransport.q_sector_transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:12:45.163179+00:00
-- url     : https://prove2.me/submissions/a2c6d9dd-da7e-4dfc-b734-eb88ccddded4

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXErrorTransport
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_BDL26CochainFamily_coboundary1_comp_coboundary0
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_cqRepresentative_difference_exists
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_selectedMap_eq_rx_of_odd_input
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_zero_outside_sector_of_zero_x_zero_q
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


section
namespace QEC
namespace Coding
namespace MultiscaleDecoder
namespace RXCoarseGraining
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
namespace RXErrorTransport
private theorem qSector_error_decomposition
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (error : D.family.Cochain1 i.succ)
    (hSupported : SupportedOn A.qCorrectionSector error) :
    error = ∑ q : Q, extendWordLinear (Lq.correctionRegion q)
      (restrictWordLinear (Lq.correctionRegion q) error) := by
  rw [extend_restrict_sum_eq_mask
    (fun q => Lq.correctionRegion q)
    A.cq_correction_regions_pairwise_disjoint error]
  funext p
  by_cases hp : p ∈ correctionRegionUnion Lq
  · change error p = if p ∈ correctionRegionUnion Lq then error p else 0
    rw [if_pos hp]
  · change error p = if p ∈ correctionRegionUnion Lq then error p else 0
    rw [if_neg hp]
    exact hSupported p (by
      intro hpq
      apply hp
      simpa [A.qCorrectionSector_eq_regions] using hpq)
private theorem qSector_boundary_eq_flow
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (error : D.family.Cochain1 i.succ)
    (hSupported : SupportedOn A.qCorrectionSector error)
    (hCocycle : ∀ q,
      A.contract.rx_local_complexes.cqDelta1 q
        (restrictWordLinear (Lq.correctionRegion q) error) = 0) :
    D.family.coboundary1 i.succ error =
      ∑ q : Q, A.contract.support_decomposition.cqFlow q
        (restrictWordLinear (Lq.correctionRegion q) error) := by
  have hdecomp := qSector_error_decomposition A error hSupported
  calc
    D.family.coboundary1 i.succ error =
        D.family.coboundary1 i.succ
          (∑ q : Q, extendWordLinear (Lq.correctionRegion q)
            (restrictWordLinear (Lq.correctionRegion q) error)) :=
      congrArg (D.family.coboundary1 i.succ) hdecomp
    _ = ∑ q : Q, D.family.coboundary1 i.succ
        (extendWordLinear (Lq.correctionRegion q)
          (restrictWordLinear (Lq.correctionRegion q) error)) := by
      rw [map_sum]
    _ = ∑ q : Q, A.contract.support_decomposition.cqFlow q
        (restrictWordLinear (Lq.correctionRegion q) error) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [A.contract.support_decomposition.cqDelta1_decomposition]
      rw [hCocycle q]
      simp
private theorem qSector_boundary_zero_on_x
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (error : D.family.Cochain1 i.succ)
    (hSupported : SupportedOn A.qCorrectionSector error)
    (hCocycle : ∀ q,
      A.contract.rx_local_complexes.cqDelta1 q
        (restrictWordLinear (Lq.correctionRegion q) error) = 0) :
    ∀ p ∈ A.xSector, (D.family.coboundary1 i.succ error) p = 0 := by
  intro p hp
  rw [qSector_boundary_eq_flow A error hSupported hCocycle]
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro q hq
  exact A.cqFlow_outside_xSector q
    (restrictWordLinear (Lq.correctionRegion q) error) p hp
private theorem qSector_boundary_zero_on_q
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (error : D.family.Cochain1 i.succ)
    (hSupported : SupportedOn A.qCorrectionSector error)
    (hCocycle : ∀ q,
      A.contract.rx_local_complexes.cqDelta1 q
        (restrictWordLinear (Lq.correctionRegion q) error) = 0) :
    ∀ p ∈ A.qSector, (D.family.coboundary1 i.succ error) p = 0 := by
  intro p hp
  rw [qSector_boundary_eq_flow A error hSupported hCocycle]
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro q hq
  exact A.contract.support_decomposition.cqFlow_outside_q_sector q
    (restrictWordLinear (Lq.correctionRegion q) error) p (by
      simpa [A.qSector_eq_regions] using hp)
end RXErrorTransport
end RXCoarseGraining
end MultiscaleDecoder
end Coding
end QEC
end

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
    (error : D.family.Cochain1 i.succ)
    (hSupported : SupportedOn A.qCorrectionSector error)
    (hCocycle : ∀ q,
      A.contract.rx_local_complexes.cqDelta1 q
        (restrictWordLinear (Lq.correctionRegion q) error) = 0) :
    ∃ lowerCorrection : D.family.Cochain1 i.castSucc,
      ∃ lowerSyndrome : D.family.Syndrome i.castSucc,
        ∃ stabilizer : D.family.Cochain0 i.succ,
          (D.rxMap i).map1 lowerCorrection =
              error + D.family.coboundary0 i.succ stabilizer ∧
          D.family.coboundary1 i.succ
              (D.family.coboundary0 i.succ stabilizer) = 0 ∧
          (lowerSyndrome : D.family.Cochain2 i.castSucc) =
              D.family.coboundary1 i.castSucc lowerCorrection ∧
          (D.selectedMap i).map2 lowerSyndrome =
              D.family.coboundary1 i.succ error ∧
          SupportedOn A.zSector ((D.selectedMap i).map2 lowerSyndrome) := by
  classical
  let qClasses := RXCoarseGrainingData.qCohomologyClass A error hCocycle
  have hRepresentativeDifference : ∀ q, ∃ s : Word Field (Q0 q),
      A.contract.rx_local_complexes.cqDelta0 q s =
        (A.cqRepresentative q (qClasses q)).1 -
          restrictWordLinear (Lq.correctionRegion q) error := by
    intro q
    exact RXCoarseGrainingData.cqRepresentative_difference_exists A error hCocycle q
  let qStabilizers : ∀ q, Word Field (Q0 q) :=
    fun q => Classical.choose (hRepresentativeDifference q)
  have hqStabilizers : ∀ q,
      A.contract.rx_local_complexes.cqDelta0 q (qStabilizers q) =
        (A.cqRepresentative q (qClasses q)).1 -
          restrictWordLinear (Lq.correctionRegion q) error := by
    intro q
    exact Classical.choose_spec (hRepresentativeDifference q)
  let lowerCorrection := A.qCohomologyEquiv qClasses
  let stabilizer : D.family.Cochain0 i.succ :=
    ∑ q : Q, A.contract.support_decomposition.cqLift0 q
      (qStabilizers q)
  have hStabilizerZero : D.family.coboundary1 i.succ
      (D.family.coboundary0 i.succ stabilizer) = 0 := by
    have hcomp := BDL26CochainFamily.coboundary1_comp_coboundary0
      D.family i.succ
    have hcomp' := LinearMap.congr_fun hcomp stabilizer
    simpa [LinearMap.comp_apply] using hcomp'
  have hErrorDecomposition := qSector_error_decomposition A error hSupported
  have hRepresentativeSum :
      (∑ q : Q, extendWordLinear (Lq.correctionRegion q)
        ((A.cqRepresentative q (qClasses q)).1)) =
      error + D.family.coboundary0 i.succ stabilizer := by
    calc
      (∑ q : Q, extendWordLinear (Lq.correctionRegion q)
          ((A.cqRepresentative q (qClasses q)).1)) =
        ∑ q : Q, (extendWordLinear (Lq.correctionRegion q)
          (restrictWordLinear (Lq.correctionRegion q) error) +
          extendWordLinear (Lq.correctionRegion q)
            (A.contract.rx_local_complexes.cqDelta0 q
              (qStabilizers q))) := by
            apply Finset.sum_congr rfl
            intro q hq
            have hqdiff := hqStabilizers q
            have hqrep :
                (A.cqRepresentative q (qClasses q)).1 =
                  restrictWordLinear (Lq.correctionRegion q) error +
                    A.contract.rx_local_complexes.cqDelta0 q
                      (qStabilizers q) := by
              have hrr :
                  restrictWordLinear (Lq.correctionRegion q) error +
                      restrictWordLinear (Lq.correctionRegion q) error =
                    (0 : Word Field
                      (LocalRegionIndex (Lq.correctionRegion q))) := by
                ext p
                exact ZModModule.add_self _
              calc
                (A.cqRepresentative q (qClasses q)).1 =
                    ((A.cqRepresentative q (qClasses q)).1 +
                      restrictWordLinear (Lq.correctionRegion q) error) +
                      restrictWordLinear (Lq.correctionRegion q) error := by
                        symm
                        rw [add_assoc, hrr, add_zero]
                _ = A.contract.rx_local_complexes.cqDelta0 q
                      (qStabilizers q) +
                      restrictWordLinear (Lq.correctionRegion q) error := by
                        rw [hqdiff, ZModModule.sub_eq_add,
                          add_assoc, hrr, add_zero]
                _ = restrictWordLinear (Lq.correctionRegion q) error +
                      A.contract.rx_local_complexes.cqDelta0 q
                        (qStabilizers q) := by abel
            rw [hqrep, map_add]
      _ = (∑ q : Q, extendWordLinear (Lq.correctionRegion q)
            (restrictWordLinear (Lq.correctionRegion q) error)) +
          (∑ q : Q, extendWordLinear (Lq.correctionRegion q)
            (A.contract.rx_local_complexes.cqDelta0 q
              (qStabilizers q))) := by
            rw [Finset.sum_add_distrib]
      _ = error + D.family.coboundary0 i.succ stabilizer := by
            rw [← hErrorDecomposition]
            rw [← A.cqDelta0_sum_decomposition]
  have hMap1 : (D.rxMap i).map1 lowerCorrection =
      error + D.family.coboundary0 i.succ stabilizer := by
    rw [A.rxMap1_eq_cqRepresentative lowerCorrection]
    simpa [lowerCorrection] using hRepresentativeSum
  let lowerSyndrome : D.family.Syndrome i.castSucc :=
    ⟨D.family.coboundary1 i.castSucc lowerCorrection, by
      exact ⟨lowerCorrection, rfl⟩⟩
  have hSelected : D.selectedMap i = D.rxMap i :=
    RXCoarseGrainingData.selectedMap_eq_rx_of_odd_input D i hOdd
  have hMap2 : (D.selectedMap i).map2 lowerSyndrome =
      D.family.coboundary1 i.succ error := by
    have hcomm := LinearMap.congr_fun (D.rxMap i).commutes_coboundary1
      lowerCorrection
    simp only [LinearMap.comp_apply] at hcomm
    rw [hMap1, map_add, hStabilizerZero, add_zero] at hcomm
    simpa [hSelected] using hcomm.symm
  have hSupport : SupportedOn A.zSector
      (D.family.coboundary1 i.succ error) :=
    RXCoarseGrainingData.zero_outside_sector_of_zero_x_zero_q A
      (qSector_boundary_zero_on_x A error hSupported hCocycle)
      (qSector_boundary_zero_on_q A error hSupported hCocycle)
  refine ⟨lowerCorrection, lowerSyndrome, stabilizer, hMap1,
    hStabilizerZero, rfl, hMap2, ?_⟩
  simpa [hMap2] using hSupport
end QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXErrorTransport

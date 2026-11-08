-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteTannerSquare.subdivisionGridVertex_eq_faceInterior_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:39:40.375205+00:00
-- url     : https://prove2.me/submissions/a3f61648-b41c-418d-962b-4caabd6d0ec6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_Core
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_TannerSquarePresentation_faceQ_injective
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
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
namespace QEC
namespace Coding
namespace BDL26FiniteTannerSquare
open BDL26FiniteAlternatingCore
open Module
attribute [instance] TannerSquareData.xFintype TannerSquareData.qFintype
  TannerSquareData.zFintype TannerSquareData.faceFintype
  TannerSquareData.xDecidableEq TannerSquareData.qDecidableEq
  TannerSquareData.zDecidableEq TannerSquareData.faceDecidableEq
namespace TannerSquarePresentation
end TannerSquarePresentation
private theorem xStarFaceXQEdge_injective
    (P : TannerSquarePresentation) (x : P.X) (f : XStarFace P x) :
    Function.Injective (xStarFaceXQEdge P x f) := by
  intro first second h
  apply P.faceQ_injective f.1
  have hvalue := congrArg Subtype.val h
  have hedge := Sum.inl.inj hvalue
  exact congrArg (fun edge : XQEdge P => edge.1.2) hedge
private theorem xStarFaceQZEdge_injective
    (P : TannerSquarePresentation) (x : P.X) (f : XStarFace P x) :
    Function.Injective (xStarFaceQZEdge P x f) := by
  intro first second h
  apply P.faceQ_injective f.1
  have hvalue := congrArg Subtype.val h
  have hedge := Sum.inr.inj hvalue
  exact congrArg (fun edge : QZEdge P => edge.1.1) hedge
set_option linter.unusedSimpArgs false in
private theorem subdivisionGridCoordinate_gridVertex
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f : XStarFace P x) (i j : Fin (S.half + 1)) :
    subdivisionGridCoordinate P x S f
        (subdivisionGridVertex P x S f i j) = some (i, j) := by
  have hm0 : S.half ≠ 0 := Nat.ne_of_gt S.half_pos
  have hxq : xStarFaceXQEdge P x f 0 ≠ xStarFaceXQEdge P x f 1 :=
    Function.Injective.ne (xStarFaceXQEdge_injective P x f) (by decide)
  have hqz : xStarFaceQZEdge P x f 0 ≠ xStarFaceQZEdge P x f 1 :=
    Function.Injective.ne (xStarFaceQZEdge_injective P x f) (by decide)
  have hqz' : xStarFaceQZEdge P x f 1 ≠ xStarFaceQZEdge P x f 0 := Ne.symm hqz
  have hq : P.faceQ f.1 0 ≠ P.faceQ f.1 1 :=
    Function.Injective.ne (P.faceQ_injective f.1) (by decide)
  by_cases hi0 : i = 0
  · subst i
    by_cases hj0 : j = 0
    · subst j
      simp [subdivisionGridVertex, subdivisionGridCoordinate, hm0,
        xStarFaceXVertex, xStarFaceQVertex, xStarFaceZVertex, hq]
    · by_cases hjm : j = gridLast S
      · subst j
        simp [gridLast, subdivisionGridVertex, subdivisionGridCoordinate,
          hm0, xStarFaceXVertex, xStarFaceQVertex, xStarFaceZVertex, hq]
      · have hj0' : j.1 ≠ 0 := by
          intro h
          apply hj0
          apply Fin.ext
          simpa using h
        have hjm' : j.1 ≠ S.half := by
          intro h
          apply hjm
          apply Fin.ext
          simpa [gridLast] using h
        simp [subdivisionGridVertex, subdivisionGridCoordinate, hm0,
          hj0', hjm', finInteriorGrid_finInteriorIndex, hxq, hqz]
  · by_cases him : i = gridLast S
    · subst i
      by_cases hj0 : j = 0
      · subst j
        simp [gridLast, subdivisionGridVertex, subdivisionGridCoordinate,
          hm0, xStarFaceXVertex, xStarFaceQVertex, xStarFaceZVertex, hq]
      · by_cases hjm : j = gridLast S
        · subst j
          simp [gridLast, subdivisionGridVertex, subdivisionGridCoordinate,
            hm0, xStarFaceXVertex, xStarFaceQVertex, xStarFaceZVertex, hq]
        · have hj0' : j.1 ≠ 0 := by
            intro h
            apply hj0
            apply Fin.ext
            simpa using h
          have hjm' : j.1 ≠ S.half := by
            intro h
            apply hjm
            apply Fin.ext
            simpa [gridLast] using h
          simp [gridLast, subdivisionGridVertex, subdivisionGridCoordinate,
            hm0, hj0', hjm', finInteriorGrid_finInteriorIndex, hxq, hqz]
    · have hi0' : i.1 ≠ 0 := by
        intro h
        apply hi0
        apply Fin.ext
        simpa using h
      have him' : i.1 ≠ S.half := by
        intro h
        apply him
        apply Fin.ext
        simpa [gridLast] using h
      by_cases hj0 : j = 0
      · subst j
        simp [subdivisionGridVertex, subdivisionGridCoordinate, hi0', him',
          hm0, finInteriorGrid_finInteriorIndex, hxq, hqz]
      · by_cases hjm : j = gridLast S
        · subst j
          simp [gridLast, subdivisionGridVertex, subdivisionGridCoordinate,
            hi0', him', hm0, finInteriorGrid_finInteriorIndex, hxq, hqz, hqz']
        · have hj0' : j.1 ≠ 0 := by
            intro h
            apply hj0
            apply Fin.ext
            simpa using h
          have hjm' : j.1 ≠ S.half := by
            intro h
            apply hjm
            apply Fin.ext
            simpa [gridLast] using h
          simp [subdivisionGridVertex, subdivisionGridCoordinate, hi0', him',
            hj0', hjm', finInteriorGrid_finInteriorIndex]
end BDL26FiniteTannerSquare
end Coding
end QEC
end

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26FiniteTannerSquare
open BDL26FiniteAlternatingCore
open Module
attribute [instance] TannerSquareData.xFintype TannerSquareData.qFintype
  TannerSquareData.zFintype TannerSquareData.faceFintype
  TannerSquareData.xDecidableEq TannerSquareData.qDecidableEq
  TannerSquareData.zDecidableEq TannerSquareData.faceDecidableEq
namespace QEC.Coding.BDL26FiniteTannerSquare
theorem _root_.solution
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (first second : XStarFace P x)
    (a b : Fin (S.half + 1)) (i j : Fin (S.half - 1))
    (h : subdivisionGridVertex P x S first a b =
      Sum.inr (Sum.inr (second, i, j))) :
    first = second ∧ a.1 = i.1 + 1 ∧ b.1 = j.1 + 1 := by
  have hdecoded := congrArg (subdivisionGridCoordinate P x S first) h
  rw [subdivisionGridCoordinate_gridVertex] at hdecoded
  simp only [subdivisionGridCoordinate] at hdecoded
  split at hdecoded <;> rename_i hface
  · have hfirst : first = second := hface.symm
    subst second
    have hcoordinates : (a, b) =
        (finInteriorGrid S i, finInteriorGrid S j) := by
      exact Option.some.inj hdecoded
    have ha := congrArg (fun pair => pair.1.1) hcoordinates
    have hb := congrArg (fun pair => pair.2.1) hcoordinates
    exact ⟨rfl, by simpa [finInteriorGrid] using ha,
      by simpa [finInteriorGrid] using hb⟩
  · cases hdecoded
end QEC.Coding.BDL26FiniteTannerSquare

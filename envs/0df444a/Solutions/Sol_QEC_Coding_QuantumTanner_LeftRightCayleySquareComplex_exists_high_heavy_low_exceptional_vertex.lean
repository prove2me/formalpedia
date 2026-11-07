-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exists_high_heavy_low_exceptional_vertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:11:10.650213+00:00
-- url     : https://prove2.me/submissions/1c12c917-65c9-439a-b59f-e7bc99308cf7

import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_DegreeSelection
import Definitions.Def_QEC_Coding_QuantumTanner_HeavySelection
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_blockLength_eq
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_blockLength
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_encodedDimension
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_heavyUnionGraph_le_unionCayleyGraph
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localExtension_apply_link
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localRestriction_localExtension
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_unionCayleyGraph_incoming_regular
import Theorems.Thm_QEC_Coding_SmallSetExpansion_exists_high_degree_low_bad_degree
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_blockLength_eq_card
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_incidence_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_mem_variableSupport_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheck_globalOperator_eq_extendLocalToRegister
import Theorems.Thm_QEC_QLDPC_QuantumCodeFamily_blockLength_eq_card
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
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Coding.QuantumTanner.Data.blockLength_eq
attribute [local simp] QEC.Coding.QuantumTanner.Family.ofData_blockLength
attribute [local simp] QEC.Coding.QuantumTanner.Family.ofData_encodedDimension
attribute [local simp] QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localExtension_apply_link
attribute [local simp] QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localRestriction_localExtension
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.FiniteQuditCheck.globalOperator_eq_extendLocalToRegister
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.blockLength_eq_card
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.incidence_iff_mem_region
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.mem_variableSupport_iff_mem_region
attribute [local simp] QEC.QLDPC.QuantumCodeFamily.blockLength_eq_card
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
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
theorem _root_.solution
    (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat)
    (normal exceptional : Finset G) (hNormal : normal.Nonempty)
    (hDegreePositive : 0 < Fintype.card A + Fintype.card B)
    (threshold badAverage badCutoff : ℝ)
    (hThreshold : 0 < threshold) (hCutoff : 0 ≤ badCutoff)
    (hHeavyCoverage : normal.card ≤ crossCount (X.heavyUnionGraph side x cutoff) normal
      (X.oppositeHeavySet side x cutoff normal))
    (hUsefulAverage : 2 * threshold * (X.oppositeHeavySet side x cutoff normal).card ≤
      (normal.card : ℝ))
    (hBadAverage : (crossCount X.unionCayleyGraph exceptional
      (X.oppositeHeavySet side x cutoff normal) : ℝ) ≤
      badAverage * (X.oppositeHeavySet side x cutoff normal).card)
    (hBudgets : badAverage * (Fintype.card A + Fintype.card B : Nat) ≤
      badCutoff * threshold) :
    ∃ h ∈ X.oppositeHeavySet side x cutoff normal,
      threshold ≤ (∑ g ∈ normal, X.heavyUnionGraph side x cutoff g h : Nat) ∧
      (∑ g ∈ exceptional, X.unionCayleyGraph g h : Nat) ≤ badCutoff := by
  let T := X.oppositeHeavySet side x cutoff normal
  let useful : G → ℝ := fun h => (∑ g ∈ normal, X.heavyUnionGraph side x cutoff g h : Nat)
  let bad : G → ℝ := fun h => (∑ g ∈ exceptional, X.unionCayleyGraph g h : Nat)
  have hT : T.Nonempty := by
    by_contra h
    have hEmpty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hZero : crossCount (X.heavyUnionGraph side x cutoff) normal T = 0 := by
      simp [crossCount, hEmpty]
    have hNormalCard := Finset.card_pos.mpr hNormal
    change normal.card ≤ crossCount (X.heavyUnionGraph side x cutoff) normal T at hHeavyCoverage
    omega
  have hUsefulBound (h : G) : useful h ≤ (Fintype.card A + Fintype.card B : Nat) := by
    have hNat : (∑ g ∈ normal, X.heavyUnionGraph side x cutoff g h) ≤
        Fintype.card A + Fintype.card B := by
      calc
        (∑ g ∈ normal, X.heavyUnionGraph side x cutoff g h) ≤
            ∑ g ∈ normal, X.unionCayleyGraph g h :=
          Finset.sum_le_sum fun g _ => X.heavyUnionGraph_le_unionCayleyGraph side x cutoff g h
        _ ≤ ∑ g : G, X.unionCayleyGraph g h := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ normal)
          intro g hg hNot
          exact Nat.zero_le _
        _ = Fintype.card A + Fintype.card B := X.unionCayleyGraph_incoming_regular h
    dsimp [useful]
    exact_mod_cast hNat
  have hUsefulSum : (∑ h ∈ T, useful h) =
      (crossCount (X.heavyUnionGraph side x cutoff) normal T : ℝ) := by
    simp only [useful, crossCount, Nat.cast_sum]
    exact Finset.sum_comm
  have hBadSum : (∑ h ∈ T, bad h) = (crossCount X.unionCayleyGraph exceptional T : ℝ) := by
    simp only [bad, crossCount, Nat.cast_sum]
    exact Finset.sum_comm
  apply exists_high_degree_low_bad_degree T hT useful bad
    (Fintype.card A + Fintype.card B : Nat) threshold badAverage badCutoff
  · exact_mod_cast hDegreePositive
  · exact hThreshold
  · exact hCutoff
  · intro h hh
    exact hUsefulBound h
  · intro h hh
    exact Nat.cast_nonneg _
  · rw [hUsefulSum]
    have hCoverage : (normal.card : ℝ) ≤
        crossCount (X.heavyUnionGraph side x cutoff) normal T := by exact_mod_cast hHeavyCoverage
    exact hUsefulAverage.trans hCoverage
  · rw [hBadSum]
    exact hBadAverage
  · exact hBudgets
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex

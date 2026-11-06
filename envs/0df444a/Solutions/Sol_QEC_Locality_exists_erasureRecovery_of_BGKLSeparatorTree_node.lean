-- Prove2me | solution 1 for QEC.Locality.exists_erasureRecovery_of_BGKLSeparatorTree_node
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:31:37.632688+00:00
-- url     : https://prove2.me/submissions/efa3a86a-6240-409f-9b7f-9c3c75df66c2

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Theorems.Thm_QEC_Locality_mem_fixedGeneratorOuterBoundaryFinset_iff
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_fixedGeneratorOuterBoundaryFinset_union_subset
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_ancestor_sum_le_distance_twentieth
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_outerBoundary_card_le_three_tenths
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_of_finiteSubsystem_subset
import Theorems.Thm_QEC_Locality_BGKLSeparatorSplit_vertices_subset_children_union_separator
import Theorems.Thm_QEC_Locality_BGKLSeparatorSplit_children_decoupled
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_of_fixedGeneratorDecoupled
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_of_fixedGeneratorOuterBoundary_subset
import Theorems.Thm_QEC_Locality_semanticStabilizerDistance_erasureRecoverableFromRegister
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
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
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
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Locality
theorem _root_.solution
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) (hd : 0 < d)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    {beta exponent : ℝ}
    (hProfile : P.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound beta exponent)
    {root : Finset ι} (globalTree : BGKLSeparatorTree P d root)
    (hSmall : (root.card : ℝ) ≤ Real.rpow
      (bgklSmallBoundaryEpsilon beta exponent * d) exponent⁻¹)
    (hRootBoundary : 4 * (fixedGeneratorOuterBoundaryFinset P root).card ≤ d)
    {vertices : Finset ι} (subtree : BGKLSeparatorTree P d vertices)
    {ancestors : List (Finset ι)}
    (hPosition : globalTree.IsNode subtree ancestors) :
    ∃ recovery : QuantumChannel (finiteSubsystemOfFinset vertices).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (finiteSubsystemOfFinset vertices).complementSystem P.semanticCode
        (finiteSubsystemOfFinset vertices).erasureChannelFromRegister recovery := by
  induction subtree generalizing ancestors with
  | leaf vertices hLeaf =>
      simpa [finiteSubsystemOfFinset, StabilizerCode.BinaryStabilizerPresentation.semanticCode]
        using semanticStabilizerDistance_erasureRecoverableFromRegister
          P.code d hDistance (finiteSubsystemOfFinset vertices) hLeaf
  | @branch vertices split large leftTree rightTree ihLeft ihRight =>
      have hLeftLocal :
          (BGKLSeparatorTree.branch split large leftTree rightTree).IsNode
            leftTree [split.separator] := by
        exact BGKLSeparatorTree.IsNode.left split large leftTree rightTree leftTree
          (BGKLSeparatorTree.IsNode.root leftTree)
      have hRightLocal :
          (BGKLSeparatorTree.branch split large leftTree rightTree).IsNode
            rightTree [split.separator] := by
        exact BGKLSeparatorTree.IsNode.right split large leftTree rightTree rightTree
          (BGKLSeparatorTree.IsNode.root rightTree)
      have hLeftPosition := hPosition.trans leftTree hLeftLocal
      have hRightPosition := hPosition.trans rightTree hRightLocal
      rcases ihLeft hLeftPosition with ⟨recoveryLeft, hRecoveryLeft⟩
      rcases ihRight hRightPosition with ⟨recoveryRight, hRecoveryRight⟩
      let leftSubsystem := finiteSubsystemOfFinset split.left
      let rightSubsystem := finiteSubsystemOfFinset split.right
      have hDecoupled : P.fixedGeneratorDecoupled
          (leftSubsystem.selected : Set ι) (rightSubsystem.selected : Set ι) := by
        simpa [leftSubsystem, rightSubsystem, finiteSubsystemOfFinset] using
          split.children_decoupled
      obtain ⟨recoveryChildren, hRecoveryChildren⟩ :=
        exists_erasureRecovery_of_fixedGeneratorDecoupled P
          leftSubsystem rightSubsystem recoveryLeft recoveryRight
          (by simpa [leftSubsystem] using hRecoveryLeft)
          (by simpa [rightSubsystem] using hRecoveryRight) hDecoupled
      let children := split.left ∪ split.right
      let childrenSubsystem := unionSubsystem leftSubsystem rightSubsystem
      have hChildrenSelected : childrenSubsystem.selected = children := by
        rfl
      let buffer := fixedGeneratorOuterBoundaryFinset P children ∪ split.separator
      let bufferSubsystem := finiteSubsystemOfFinset buffer
      have hLeftBoundary := hLeftPosition.outerBoundary_card_le_three_tenths
        hd hProfile hSmall hRootBoundary
      have hRightBoundary := hRightPosition.outerBoundary_card_le_three_tenths
        hd hProfile hSmall hRootBoundary
      have hChildrenBoundarySubset :=
        fixedGeneratorOuterBoundaryFinset_union_subset P split.left split.right
      have hChildrenBoundaryCard :
          (fixedGeneratorOuterBoundaryFinset P children).card ≤
            (fixedGeneratorOuterBoundaryFinset P split.left).card +
              (fixedGeneratorOuterBoundaryFinset P split.right).card := by
        exact (Finset.card_le_card hChildrenBoundarySubset).trans (Finset.card_union_le _ _)
      have hAncestorBudget := hLeftPosition.ancestor_sum_le_distance_twentieth
        hd hProfile hSmall
      have hSeparatorInBudget : split.separator.card ≤
          ancestorSeparatorCardSum (ancestors ++ [split.separator]) := by
        simp [ancestorSeparatorCardSum]
      have hSeparatorReal : (split.separator.card : ℝ) ≤ (d : ℝ) / 20 := by
        have hCast : (split.separator.card : ℝ) ≤
            (ancestorSeparatorCardSum (ancestors ++ [split.separator]) : ℝ) := by
          exact_mod_cast hSeparatorInBudget
        exact hCast.trans hAncestorBudget
      have hBufferCardNat : buffer.card ≤
          (fixedGeneratorOuterBoundaryFinset P children).card + split.separator.card := by
        exact Finset.card_union_le _ _
      have hBufferCardReal : (buffer.card : ℝ) ≤ 13 * (d : ℝ) / 20 := by
        have hChildrenBoundaryCardReal :
            ((fixedGeneratorOuterBoundaryFinset P children).card : ℝ) ≤
              ((fixedGeneratorOuterBoundaryFinset P split.left).card : ℝ) +
                ((fixedGeneratorOuterBoundaryFinset P split.right).card : ℝ) := by
          exact_mod_cast hChildrenBoundaryCard
        have hBufferCardCast : (buffer.card : ℝ) ≤
            ((fixedGeneratorOuterBoundaryFinset P children).card : ℝ) +
              (split.separator.card : ℝ) := by
          exact_mod_cast hBufferCardNat
        linarith
      have hBufferSmall : buffer.card < d := by
        have hdReal : (0 : ℝ) < d := by exact_mod_cast hd
        exact_mod_cast (hBufferCardReal.trans_lt (by linarith : 13 * (d : ℝ) / 20 < d))
      obtain ⟨recoveryBuffer, hRecoveryBuffer⟩ :=
        semanticStabilizerDistance_erasureRecoverableFromRegister
          P.code d hDistance bufferSubsystem (by
            simpa [bufferSubsystem, finiteSubsystemOfFinset] using hBufferSmall)
      have hBoundary : P.fixedGeneratorOuterBoundary
          (childrenSubsystem.selected : Set ι) ⊆ (bufferSubsystem.selected : Set ι) := by
        intro q hq
        have hqFinset : q ∈ fixedGeneratorOuterBoundaryFinset P children := by
          rw [mem_fixedGeneratorOuterBoundaryFinset_iff]
          simpa [hChildrenSelected] using hq
        simp [bufferSubsystem, finiteSubsystemOfFinset, buffer, hqFinset]
      obtain ⟨recoveryExpanded, hRecoveryExpanded⟩ :=
        exists_erasureRecovery_of_fixedGeneratorOuterBoundary_subset
          P childrenSubsystem bufferSubsystem recoveryChildren recoveryBuffer
          (by simpa [childrenSubsystem] using hRecoveryChildren)
          (by simpa [StabilizerCode.BinaryStabilizerPresentation.semanticCode]
            using hRecoveryBuffer) hBoundary
      have hParentSubset : (finiteSubsystemOfFinset vertices).selected ⊆
          (unionSubsystem childrenSubsystem bufferSubsystem).selected := by
        intro q hq
        have hqCover := split.vertices_subset_children_union_separator hq
        rcases Finset.mem_union.mp hqCover with hqChildren | hqSeparator
        · apply Finset.mem_union_left
          rw [hChildrenSelected]
          exact hqChildren
        · exact Finset.mem_union_right _ (by
            simp [bufferSubsystem, finiteSubsystemOfFinset, buffer, hqSeparator])
      exact exists_erasureRecovery_of_finiteSubsystem_subset
        (finiteSubsystemOfFinset vertices)
        (unionSubsystem childrenSubsystem bufferSubsystem) hParentSubset P.semanticCode
        ⟨recoveryExpanded, hRecoveryExpanded⟩
end QEC.Locality

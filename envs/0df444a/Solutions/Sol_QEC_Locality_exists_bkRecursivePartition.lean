-- Prove2me | solution 1 for QEC.Locality.exists_bkRecursivePartition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:12:58.070214+00:00
-- url     : https://prove2.me/submissions/1938ba2c-0309-4a91-9e3c-ec335398a270

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Theorems.Thm_QEC_Locality_measuredTwoThirdsLeft_subset
import Theorems.Thm_QEC_Locality_measuredTwoThirdsRight_subset
import Theorems.Thm_QEC_Locality_bkSeparatorRecurrence_eq_profile_add
import Theorems.Thm_QEC_Locality_NoEdgeBetween_mono
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_minimumTwoThirdsBalancedVertexSeparatorSize_le_twoThirdsSeparationProfile
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
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (G : ConnectivityGraph ι) (d : Nat) (hd : 0 < d) (vertices : Finset ι) :
    Nonempty (BKRecursivePartition G d vertices) := by
  induction vertices using (measure Finset.card).wf.induction with
  | h vertices ih =>
      classical
      by_cases hterminal : bkSeparatorTerminal d vertices
      · have hsmall : vertices.card < d := by
          rcases hterminal with hempty | hsmall
          · subst vertices
            simpa using hd
          · exact hsmall
        refine ⟨{
          pieces := {vertices}
          remainder := ∅
          piece_subset := ?_
          remainder_subset := ?_
          covers := ?_
          pieces_remainder_disjoint := ?_
          piece_card_lt := ?_
          pairwise_decoupled := ?_
          remainder_card_le := ?_ }⟩
        · intro piece hpiece
          have : piece = vertices := Finset.mem_singleton.mp hpiece
          subst piece
          exact subset_rfl
        · simp
        · simp
        · simp
        · intro piece hpiece
          have : piece = vertices := Finset.mem_singleton.mp hpiece
          subst piece
          exact hsmall
        · intro left hleft right hright hne
          simp at hleft hright
          subst left
          subst right
          exact (hne rfl).elim
        · simp [bkSeparatorRecurrence, hterminal]
      · have hnonempty : vertices.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hempty
          exact hterminal (Or.inl hempty)
        let left := measuredTwoThirdsLeft G vertices
        let right := measuredTwoThirdsRight G vertices
        let separator := measuredTwoThirdsSeparator G vertices
        have hleft_lt : left.card < vertices.card := by
          exact measuredTwoThirdsLeft_card_lt G vertices hnonempty
        have hright_lt : right.card < vertices.card := by
          exact measuredTwoThirdsRight_card_lt G vertices hnonempty
        rcases ih left hleft_lt with ⟨leftPartition⟩
        rcases ih right hright_lt with ⟨rightPartition⟩
        have hsplit : TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right := by
          exact measuredTwoThirdsSplit_spec G vertices
        let pieces := leftPartition.pieces ∪ rightPartition.pieces
        let remainder := separator ∪ leftPartition.remainder ∪ rightPartition.remainder
        have hleft_subset : left ⊆ vertices := measuredTwoThirdsLeft_subset G vertices
        have hright_subset : right ⊆ vertices := measuredTwoThirdsRight_subset G vertices
        have hseparator_subset : separator ⊆ vertices := hsplit.1
        refine ⟨{
          pieces := pieces
          remainder := remainder
          piece_subset := ?_
          remainder_subset := ?_
          covers := ?_
          pieces_remainder_disjoint := ?_
          piece_card_lt := ?_
          pairwise_decoupled := ?_
          remainder_card_le := ?_ }⟩
        · intro piece hpiece
          rcases Finset.mem_union.mp hpiece with hpiece | hpiece
          · exact (leftPartition.piece_subset piece hpiece).trans hleft_subset
          · exact (rightPartition.piece_subset piece hpiece).trans hright_subset
        · exact Finset.union_subset
            (Finset.union_subset hseparator_subset
              (leftPartition.remainder_subset.trans hleft_subset))
            (rightPartition.remainder_subset.trans hright_subset)
        · dsimp [pieces, remainder]
          ext x
          constructor
          · intro hx
            rcases Finset.mem_union.mp hx with hxpieces | hxremainder
            · rcases Finset.mem_biUnion.mp hxpieces with ⟨piece, hp, hxp⟩
              rcases Finset.mem_union.mp hp with hp | hp
              · exact hleft_subset (leftPartition.piece_subset piece hp hxp)
              · exact hright_subset (rightPartition.piece_subset piece hp hxp)
            · rcases Finset.mem_union.mp hxremainder with hxseparatorOrLeft | hxright
              rcases Finset.mem_union.mp hxseparatorOrLeft with hxseparator | hxleft
              · exact hseparator_subset hxseparator
              · exact hleft_subset (leftPartition.remainder_subset hxleft)
              · exact hright_subset (rightPartition.remainder_subset hxright)
          · intro hx
            by_cases hxsep : x ∈ separator
            · exact Finset.mem_union_right _
                (Finset.mem_union_left _ (Finset.mem_union_left _ hxsep))
            · have hxdiff : x ∈ vertices \ separator := Finset.mem_sdiff.mpr ⟨hx, hxsep⟩
              rw [← hsplit.2.1] at hxdiff
              rcases Finset.mem_union.mp hxdiff with hxleft | hxright
              · have hcovered : x ∈ leftPartition.pieces.biUnion id ∪
                    leftPartition.remainder := by
                  rw [leftPartition.covers]
                  exact hxleft
                rcases Finset.mem_union.mp hcovered with hxpieces | hxrem
                · rcases Finset.mem_biUnion.mp hxpieces with ⟨piece, hp, hxp⟩
                  exact Finset.mem_union_left _
                    (Finset.mem_biUnion.mpr ⟨piece, Finset.mem_union_left _ hp, hxp⟩)
                · exact Finset.mem_union_right _
                    (Finset.mem_union_left _ (Finset.mem_union_right _ hxrem))
              · have hcovered : x ∈ rightPartition.pieces.biUnion id ∪
                    rightPartition.remainder := by
                  rw [rightPartition.covers]
                  exact hxright
                rcases Finset.mem_union.mp hcovered with hxpieces | hxrem
                · rcases Finset.mem_biUnion.mp hxpieces with ⟨piece, hp, hxp⟩
                  exact Finset.mem_union_left _
                    (Finset.mem_biUnion.mpr ⟨piece, Finset.mem_union_right _ hp, hxp⟩)
                · exact Finset.mem_union_right _ (Finset.mem_union_right _ hxrem)
        · dsimp [pieces, remainder]
          apply Finset.disjoint_left.mpr
          intro x hxpieces hxremainder
          rcases Finset.mem_biUnion.mp hxpieces with ⟨piece, hpiece, hxpiece⟩
          rcases Finset.mem_union.mp hpiece with hpieceLeft | hpieceRight
          · have hxleft : x ∈ left := leftPartition.piece_subset piece hpieceLeft hxpiece
            rcases Finset.mem_union.mp hxremainder with hxseparatorOrLeft | hxrightRem
            · rcases Finset.mem_union.mp hxseparatorOrLeft with hxseparator | hxleftRem
              · have hxdiff : x ∈ vertices \ separator := by
                  rw [← hsplit.2.1]
                  exact Finset.mem_union_left _ hxleft
                exact (Finset.mem_sdiff.mp hxdiff).2 hxseparator
              · exact (Finset.disjoint_left.mp leftPartition.pieces_remainder_disjoint)
                  (Finset.mem_biUnion.mpr ⟨piece, hpieceLeft, hxpiece⟩) hxleftRem
            · exact (Finset.disjoint_left.mp hsplit.2.2.1) hxleft
                (rightPartition.remainder_subset hxrightRem)
          · have hxright : x ∈ right := rightPartition.piece_subset piece hpieceRight hxpiece
            rcases Finset.mem_union.mp hxremainder with hxseparatorOrLeft | hxrightRem
            · rcases Finset.mem_union.mp hxseparatorOrLeft with hxseparator | hxleftRem
              · have hxdiff : x ∈ vertices \ separator := by
                  rw [← hsplit.2.1]
                  exact Finset.mem_union_right _ hxright
                exact (Finset.mem_sdiff.mp hxdiff).2 hxseparator
              · exact (Finset.disjoint_left.mp hsplit.2.2.1)
                  (leftPartition.remainder_subset hxleftRem) hxright
            · exact (Finset.disjoint_left.mp rightPartition.pieces_remainder_disjoint)
                (Finset.mem_biUnion.mpr ⟨piece, hpieceRight, hxpiece⟩) hxrightRem
        · intro piece hpiece
          rcases Finset.mem_union.mp hpiece with hpiece | hpiece
          · exact leftPartition.piece_card_lt piece hpiece
          · exact rightPartition.piece_card_lt piece hpiece
        · intro pieceA hA pieceB hB hne
          rcases Finset.mem_union.mp hA with hAL | hAR
          · rcases Finset.mem_union.mp hB with hBL | hBR
            · exact leftPartition.pairwise_decoupled pieceA hAL pieceB hBL hne
            · refine ⟨?_, ?_⟩
              · apply Finset.disjoint_left.mpr
                intro x hxA hxB
                exact (Finset.disjoint_left.mp hsplit.2.2.1)
                  (leftPartition.piece_subset pieceA hAL hxA)
                  (rightPartition.piece_subset pieceB hBR hxB)
              · exact hsplit.2.2.2.2.2.mono
                  (leftPartition.piece_subset pieceA hAL)
                  (rightPartition.piece_subset pieceB hBR)
          · rcases Finset.mem_union.mp hB with hBL | hBR
            · refine ⟨?_, ?_⟩
              · apply Finset.disjoint_left.mpr
                intro x hxA hxB
                exact (Finset.disjoint_left.mp hsplit.2.2.1)
                  (leftPartition.piece_subset pieceB hBL hxB)
                  (rightPartition.piece_subset pieceA hAR hxA)
              · exact (hsplit.2.2.2.2.2.mono
                  (leftPartition.piece_subset pieceB hBL)
                  (rightPartition.piece_subset pieceA hAR)).symm
            · exact rightPartition.pairwise_decoupled pieceA hAR pieceB hBR hne
        · dsimp [remainder]
          calc
            (separator ∪ leftPartition.remainder ∪ rightPartition.remainder).card
                ≤ (separator ∪ leftPartition.remainder).card + rightPartition.remainder.card :=
              Finset.card_union_le _ _
            _ ≤ separator.card + leftPartition.remainder.card + rightPartition.remainder.card := by
              exact Nat.add_le_add_right (Finset.card_union_le _ _) _
            _ ≤ separator.card + bkSeparatorRecurrence G d left +
                  bkSeparatorRecurrence G d right := by
              exact Nat.add_le_add
                (Nat.add_le_add_left leftPartition.remainder_card_le separator.card)
                rightPartition.remainder_card_le
            _ ≤ twoThirdsSeparationProfile G vertices.card +
                  bkSeparatorRecurrence G d left + bkSeparatorRecurrence G d right := by
              have hseparatorProfile : separator.card ≤
                  twoThirdsSeparationProfile G vertices.card := by
                rw [(measuredTwoThirdsSeparator_spec G vertices).2.2]
                exact minimumTwoThirdsBalancedVertexSeparatorSize_le_twoThirdsSeparationProfile
                  G vertices.card vertices (by simp) le_rfl
              omega
            _ = bkSeparatorRecurrence G d vertices := by
              exact (bkSeparatorRecurrence_eq_profile_add G d vertices hterminal).symm
end QEC.Locality

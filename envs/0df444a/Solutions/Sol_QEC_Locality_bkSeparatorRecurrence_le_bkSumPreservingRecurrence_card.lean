-- Prove2me | solution 1 for QEC.Locality.bkSeparatorRecurrence_le_bkSumPreservingRecurrence_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:30:56.036196+00:00
-- url     : https://prove2.me/submissions/d47c228a-1ade-481d-802f-2a253abda23a

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Theorems.Thm_QEC_Locality_bkSumPreservingRecurrence_eq_profile_add
import Theorems.Thm_QEC_Locality_measuredTwoThirdsChildren_mem_bkAdmissibleChildPairs
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_bkSeparatorRecurrence_eq_profile_add
import Theorems.Thm_QEC_Locality_bkSeparatorRecurrence_eq_zero_of_terminal
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
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (G : ConnectivityGraph ι) (d : Nat) (vertices : Finset ι) :
    bkSeparatorRecurrence G d vertices ≤
      bkSumPreservingRecurrence G d vertices.card := by
  induction vertices using (measure Finset.card).wf.induction with
  | h vertices ih =>
      by_cases hterminal : bkSeparatorTerminal d vertices
      · rw [bkSeparatorRecurrence_eq_zero_of_terminal G d vertices hterminal]
        exact Nat.zero_le _
      · have hnonempty : vertices.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hempty
          exact hterminal (Or.inl hempty)
        let left := measuredTwoThirdsLeft G vertices
        let right := measuredTwoThirdsRight G vertices
        have hleftLt : left.card < vertices.card :=
          measuredTwoThirdsLeft_card_lt G vertices hnonempty
        have hrightLt : right.card < vertices.card :=
          measuredTwoThirdsRight_card_lt G vertices hnonempty
        have hleftBound := ih left hleftLt
        have hrightBound := ih right hrightLt
        have hpair : (left.card, right.card) ∈
            bkAdmissibleChildPairs vertices.card := by
          exact measuredTwoThirdsChildren_mem_bkAdmissibleChildPairs G vertices hnonempty
        have hchildren :
            bkSumPreservingRecurrence G d left.card +
                bkSumPreservingRecurrence G d right.card ≤
              (bkAdmissibleChildPairs vertices.card).sup (fun children =>
                if hchildren : children ∈ bkAdmissibleChildPairs vertices.card then
                  bkSumPreservingRecurrence G d children.1 +
                    bkSumPreservingRecurrence G d children.2
                else 0) := by
          have hsup := Finset.le_sup
            (f := fun children : Nat × Nat =>
              if hchildren : children ∈ bkAdmissibleChildPairs vertices.card then
                bkSumPreservingRecurrence G d children.1 +
                  bkSumPreservingRecurrence G d children.2
              else 0) hpair
          simpa [hpair] using hsup
        have hscaleNonterminal : ¬bkScaleTerminal d vertices.card := by
          intro hscale
          rcases hscale with hcardZero | hcardSmall
          · apply hterminal
            left
            exact Finset.card_eq_zero.mp hcardZero
          · exact hterminal (Or.inr hcardSmall)
        rw [bkSeparatorRecurrence_eq_profile_add G d vertices hterminal]
        rw [bkSumPreservingRecurrence_eq_profile_add G d vertices.card hscaleNonterminal]
        have hrecursive := (Nat.add_le_add hleftBound hrightBound).trans hchildren
        simpa [left, right, Nat.add_assoc] using
          Nat.add_le_add_left hrecursive (twoThirdsSeparationProfile G vertices.card)
end QEC.Locality

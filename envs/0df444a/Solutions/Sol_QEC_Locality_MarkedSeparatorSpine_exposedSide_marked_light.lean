-- Prove2me | solution 1 for QEC.Locality.MarkedSeparatorSpine.exposedSide_marked_light
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:44:27.98309+00:00
-- url     : https://prove2.me/submissions/861d8e84-f674-42cb-9258-86105b35a01f

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_terminalCarrier_subset
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_subset
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_NoEdgeBetween_mono
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


attribute [local simp] QEC.Locality.MarkedSeparatorSpine.exposedSide_stop
section
namespace QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
private theorem MarkedSeparatorSpine.exposedSide_disjoint_terminalCarrier
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    Disjoint spine.exposedSide spine.terminalCarrier := by
  induction spine with
  | stop hpartition hminimum hleftLight hrightLight =>
      simpa [exposedSide, terminalCarrier] using
        (Finset.disjoint_empty_left vertices)
  | @followLeft vertices left separator right hpartition hminimum hleftHeavy subtree ih =>
      apply Finset.disjoint_left.mpr
      intro x hxexposed hxterminal
      rcases Finset.mem_union.mp hxexposed with hxright | hxsub
      · have hxleft := subtree.terminalCarrier_subset hxterminal
        exact (Finset.disjoint_left.mp hpartition.2.2.1) hxleft hxright
      · exact (Finset.disjoint_left.mp ih) hxsub hxterminal
  | @followRight vertices left separator right hpartition hminimum hrightHeavy subtree ih =>
      apply Finset.disjoint_left.mpr
      intro x hxexposed hxterminal
      rcases Finset.mem_union.mp hxexposed with hxleft | hxsub
      · have hxright := subtree.terminalCarrier_subset hxterminal
        exact (Finset.disjoint_left.mp hpartition.2.2.1) hxleft hxright
      · exact (Finset.disjoint_left.mp ih) hxsub hxterminal
private theorem MarkedSeparatorSpine.terminalCarrier_eq_or_marked_heavy
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    spine.terminalCarrier = vertices ∨
      2 * marked.card < 3 * (marked ∩ spine.terminalCarrier).card := by
  induction spine with
  | stop hpartition hminimum hleftLight hrightLight =>
      exact Or.inl rfl
  | followLeft hpartition hminimum hleftHeavy subtree ih =>
      rcases ih with hterminal | hterminal
      · exact Or.inr (by simpa [terminalCarrier, hterminal] using hleftHeavy)
      · exact Or.inr (by simpa [terminalCarrier] using hterminal)
  | followRight hpartition hminimum hrightHeavy subtree ih =>
      rcases ih with hterminal | hterminal
      · exact Or.inr (by simpa [terminalCarrier, hterminal] using hrightHeavy)
      · exact Or.inr (by simpa [terminalCarrier] using hterminal)
end QEC.Locality
end

set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
namespace MarkedSeparatorSpine
theorem _root_.solution
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    3 * (marked ∩ spine.exposedSide).card ≤ 2 * marked.card := by
  rcases spine.terminalCarrier_eq_or_marked_heavy with hterminal | hheavy
  · have hempty : spine.exposedSide = ∅ := by
      by_contra hne
      have hnonempty : spine.exposedSide.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
      rcases hnonempty with ⟨x, hx⟩
      exact (Finset.disjoint_left.mp spine.exposedSide_disjoint_terminalCarrier)
        hx (by rw [hterminal]; exact spine.exposedSide_subset hx)
    simp [hempty]
  · have hdisjoint : Disjoint (marked ∩ spine.exposedSide)
        (marked ∩ spine.terminalCarrier) := by
      exact Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right
        spine.exposedSide_disjoint_terminalCarrier
    have hunion : (marked ∩ spine.exposedSide).card +
        (marked ∩ spine.terminalCarrier).card ≤ marked.card := by
      rw [← Finset.card_union_of_disjoint hdisjoint]
      exact Finset.card_le_card (Finset.union_subset
        Finset.inter_subset_left Finset.inter_subset_left)
    omega
end MarkedSeparatorSpine
end QEC.Locality

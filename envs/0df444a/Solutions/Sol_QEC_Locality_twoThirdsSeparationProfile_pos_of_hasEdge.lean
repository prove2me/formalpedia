-- Prove2me | solution 1 for QEC.Locality.twoThirdsSeparationProfile_pos_of_hasEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:08:16.913853+00:00
-- url     : https://prove2.me/submissions/d89194a5-bdc0-4bcc-853c-be19617688ff

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Locality_exists_minimumTwoThirdsBalancedVertexSeparator
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
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
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
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v
namespace QEC.Locality
theorem _root_.solution
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (hEdge : G.HasEdge) {scale : Nat}
    (hscale : 2 ≤ scale) :
    0 < twoThirdsSeparationProfile G scale := by
  rcases hEdge with ⟨p, q, hpq⟩
  have hpne : p ≠ q := by
    intro hpqEq
    subst q
    exact G.loopless p hpq
  let vertices : Finset ι := {p, q}
  have hverticesCard : vertices.card = 2 := by
    simp [vertices, hpne]
  have hminimumPos :
      0 < minimumTwoThirdsBalancedVertexSeparatorSize G vertices := by
    apply Nat.pos_of_ne_zero
    intro hminimumZero
    rcases exists_minimumTwoThirdsBalancedVertexSeparator G vertices with
      ⟨separator, _hseparatorSubset, hbalanced, hseparatorCard⟩
    have hseparatorEmpty : separator = ∅ := by
      apply Finset.card_eq_zero.mp
      rw [hseparatorCard, hminimumZero]
    subst separator
    rcases hbalanced with
      ⟨left, right, _hemptySubset, hpartition, _hdisjoint,
        hleftBalanced, hrightBalanced, hnoEdge⟩
    have hpartition' : left ∪ right = vertices := by
      simpa using hpartition
    have hpSide : p ∈ left ∨ p ∈ right := by
      have : p ∈ left ∪ right := by
        rw [hpartition']
        simp [vertices]
      exact Finset.mem_union.mp this
    have hqSide : q ∈ left ∨ q ∈ right := by
      have : q ∈ left ∪ right := by
        rw [hpartition']
        simp [vertices]
      exact Finset.mem_union.mp this
    rcases hpSide with hpLeft | hpRight
    · rcases hqSide with hqLeft | hqRight
      · have hverticesSubset : vertices ⊆ left := by
          intro x hx
          simp only [vertices, Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hpLeft
          · exact hqLeft
        have htwoLe : 2 ≤ left.card := by
          simpa [hverticesCard] using Finset.card_le_card hverticesSubset
        omega
      · exact (hnoEdge hpLeft hqRight) hpq
    · rcases hqSide with hqLeft | hqRight
      · exact (hnoEdge hqLeft hpRight) (G.symmetric hpq)
      · have hverticesSubset : vertices ⊆ right := by
          intro x hx
          simp only [vertices, Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hpRight
          · exact hqRight
        have htwoLe : 2 ≤ right.card := by
          simpa [hverticesCard] using Finset.card_le_card hverticesSubset
        omega
  have hminimumLeProfile :
      minimumTwoThirdsBalancedVertexSeparatorSize G vertices ≤
        twoThirdsSeparationProfile G scale := by
    apply minimumTwoThirdsBalancedVertexSeparatorSize_le_twoThirdsSeparationProfile
    · simp
    · omega
  omega
end QEC.Locality

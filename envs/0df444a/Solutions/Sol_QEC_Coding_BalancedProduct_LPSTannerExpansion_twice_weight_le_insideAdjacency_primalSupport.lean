-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSTannerExpansion.twice_weight_le_insideAdjacency_primalSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:45:28.096161+00:00
-- url     : https://prove2.me/submissions/53d26dfb-2ab7-405d-b769-5a1e7c651e5a

import Definitions.Def_QEC_Coding_BalancedProduct_LPSTanner
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTannerExpansion
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_localView_weight_eq_support_degree
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_sum_localView_weight_eq_twice_globalWeight
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_mem_primalSupportVertices_iff
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_mem_lpsNeighbors401_iff_adj
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_checkBlock_basis_same
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_incidentAsEdge_edgeAsIncident
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
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
attribute [local simp] QEC.Coding.BalancedProduct.LPSTanner.checkBlock_basis_same
attribute [local simp] QEC.Coding.BalancedProduct.LPSTanner.incidentAsEdge_edgeAsIncident
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
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSTannerExpansion
open Classical
open QEC.Coding
open QEC.Coding.BalancedProduct
open LPSTanner LPSGraph GVPlus
namespace QEC.Coding.BalancedProduct.LPSTannerExpansion
theorem _root_.solution
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    2 * HammingWeight x ≤
      insideAdjacencyCount401 q hq
        (primalSupportVertices q hq40 hq x) := by
  let S := primalSupportVertices q hq40 hq x
  have hsumS :
      (∑ g ∈ S, HammingWeight (localView q hq40 hq g x)) =
        2 * HammingWeight x := by
    rw [← sum_localView_weight_eq_twice_globalWeight q hq40 hq x]
    apply Finset.sum_subset (Finset.subset_univ S)
    intro g _hgUniv hgS
    have hzero : localView q hq40 hq g x = 0 := by
      by_contra hne
      exact hgS ((mem_primalSupportVertices_iff q hq40 hq x g).2 hne)
    rw [hzero]
    simp
  have hdegree (g : Vertex401 q) (hg : g ∈ S) :
      HammingWeight (localView q hq40 hq g x) ≤
        (lpsNeighborsIn401 q hq S g).card := by
    rw [localView_weight_eq_support_degree q hq40 hq x]
    apply Finset.card_le_card
    intro w hw
    have hsupport : (wordSupportGraph q hq x).Adj g w := by
      simpa using hw
    have hlps : (lpsCayleyGraph401 q hq).Adj g w :=
      (wordSupportGraph_le_lps q hq x) hsupport
    have hdegreePos : 0 < (wordSupportGraph q hq x).degree w :=
      SimpleGraph.Adj.degree_pos_right hsupport
    have hlocalPos : 0 < HammingWeight (localView q hq40 hq w x) := by
      rw [localView_weight_eq_support_degree q hq40 hq x]
      exact hdegreePos
    have hwS : w ∈ S :=
      (mem_primalSupportVertices_iff q hq40 hq x w).2 <|
        (HammingWeight_eq_zero_iff _).not.mp (Nat.ne_of_gt hlocalPos)
    exact Finset.mem_filter.2
      ⟨(LPSGraph.mem_lpsNeighbors401_iff_adj q hq g w).2 hlps, hwS⟩
  calc
    2 * HammingWeight x =
        ∑ g ∈ S, HammingWeight (localView q hq40 hq g x) := hsumS.symm
    _ ≤ ∑ g ∈ S, (lpsNeighborsIn401 q hq S g).card := by
      exact Finset.sum_le_sum fun g hg => hdegree g hg
    _ = insideAdjacencyCount401 q hq S := by
      rfl
end QEC.Coding.BalancedProduct.LPSTannerExpansion

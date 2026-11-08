-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSTannerExpansion.dualExposedVertices_expansion401
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:47:09.403417+00:00
-- url     : https://prove2.me/submissions/636e0dcd-641b-4560-a722-955b6b0a9374

import Definitions.Def_QEC_Coding_BalancedProduct_LPSTanner
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTannerExpansion
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_card_dualSupportVertices_le_weight
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_weight_le_200_mul_card_dualSupportVertices
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_dualSupport_card_eq_exposed_add_unexposed
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_fortyOne_mul_unexposed_le_insideAdjacency
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_card_check401_eq
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_smallSet_insideAdjacency401
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
    (hLPS : LPS401RayleighBound q hq)
    (y : Word (ZMod 2) (Check401 q))
    (hy : 10000000 * HammingWeight y ≤ Fintype.card (Check401 q)) :
    11 * HammingWeight y ≤
      102500 * (dualExposedVertices q hq40 hq y).card := by
  let U := dualSupportVertices q y
  let X := dualExposedVertices q hq40 hq y
  let B := dualUnexposedSupportVertices q hq40 hq y
  let D := insideAdjacencyCount401 q hq U
  have hUCard := card_dualSupportVertices_le_weight q y
  have hUCard' : U.card ≤ HammingWeight y := by simpa [U] using hUCard
  rw [card_check401_eq q] at hy
  have hsmall : 10000000 * U.card ≤
      402 * Fintype.card (Vertex401 q) := by
    omega
  have hspectral : 25 * D ≤ 1003 * U.card :=
    smallSet_insideAdjacency401 q hq40 hq hLPS U hsmall
  have hbad : 41 * B.card ≤ D := by
    simpa [B, D, U] using
      fortyOne_mul_unexposed_le_insideAdjacency q hq40 hq y
  have hpartition : U.card = X.card + B.card := by
    simpa [U, X, B] using
      dualSupport_card_eq_exposed_add_unexposed q hq40 hq y
  have hweight := weight_le_200_mul_card_dualSupportVertices q y
  have hweight' : HammingWeight y ≤ 200 * U.card := by simpa [U] using hweight
  have hresult : 11 * HammingWeight y ≤ 102500 * X.card := by
    omega
  simpa [X] using hresult
end QEC.Coding.BalancedProduct.LPSTannerExpansion

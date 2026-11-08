-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSTannerExpansion.nonempty_dualExposure_of_inside_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:43:00.711549+00:00
-- url     : https://prove2.me/submissions/cd98cc4c-667e-4be7-821f-f8848e28ca03

import Definitions.Def_QEC_Coding_BalancedProduct_LPSTanner
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTannerExpansion
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_mem_dualSupportVertices_iff
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_card_dualSupportedNeighbors
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_dualSupportedNeighbors_subset_lps
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_checkBlock_basis_same
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_incidentAsEdge_edgeAsIncident
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_localTranspose_weight_lower_bound
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
    (y : Word (ZMod 2) (Check401 q))
    (g : Vertex401 q)
    (hg : g ∈ dualSupportVertices q y)
    (hinside : (lpsNeighborsIn401 q hq (dualSupportVertices q y) g).card < 41) :
    Nonempty (DualExposureWitness q hq40 hq y g) := by
  let U := dualSupportVertices q y
  let z := wordLinearMapTranspose localParityCheck (checkBlock q g y)
  let N := dualSupportedNeighbors q hq40 hq y g
  have hblock : checkBlock q g y ≠ 0 :=
    (mem_dualSupportVertices_iff q y g).1 hg
  have hzWeight : 41 ≤ HammingWeight z :=
    localTranspose_weight_lower_bound (checkBlock q g y) hblock
  have hNCard : 41 ≤ N.card := by
    rw [card_dualSupportedNeighbors q hq40 hq y g]
    exact hzWeight
  have hnotSubset : ¬N ⊆ lpsNeighborsIn401 q hq U g := by
    intro hsub
    have hcard := Finset.card_le_card hsub
    change (lpsNeighborsIn401 q hq U g).card < 41 at hinside
    omega
  rcases Finset.not_subset.mp hnotSubset with ⟨w, hwN, hwOutside⟩
  have hwLPS : w ∈ lpsNeighbors401 q hq g :=
    dualSupportedNeighbors_subset_lps q hq40 hq y g hwN
  have hwNotU : w ∉ U := by
    intro hwU
    exact hwOutside (Finset.mem_filter.2 ⟨hwLPS, hwU⟩)
  let E := localCoordinateNeighborEquiv q hq40 hq g
  let emb : LocalCoordinate ↪ Vertex401 q :=
    E.toEmbedding.trans (Function.Embedding.subtype _)
  change w ∈ (hammingSupport z).map emb at hwN
  rcases Finset.mem_map.1 hwN with ⟨a, ha, haw⟩
  have hza : z a ≠ 0 := by
    simpa [hammingSupport] using ha
  let Λ := incidentCoordinateEquiv q hq40 hq g
  let i := Λ.symm a
  let e : Edge401 q hq := incidentAsEdge q hq i
  have hendpoint : g ∈ e.1 := i.2.2
  have hedgeIncident : edgeAsIncident q hq e g hendpoint = i := by
    apply Subtype.ext
    rfl
  have hcoord : edgeLocalCoordinate q hq40 hq e g hendpoint = a := by
    change Λ (edgeAsIncident q hq e g hendpoint) = a
    rw [hedgeIncident]
    exact Λ.apply_symm_apply a
  have hi : i.1 = s(g, (E a).1) := by
    have h := ((lpsCayleyGraph401 q hq).incidenceSetEquivNeighborSet g).symm_apply_apply i
    exact (congrArg Subtype.val h).symm
  have hEa : (E a).1 = w := by
    exact haw
  have heval : e.1 = s(g, w) := by
    change i.1 = s(g, w)
    rw [hi, hEa]
  have hwBlockZero : checkBlock q w y = 0 := by
    by_contra hne
    exact hwNotU ((mem_dualSupportVertices_iff q y w).2 hne)
  refine ⟨{
    edge := e
    endpoint := hendpoint
    centerNonzero := hblock
    localNonzero := ?_
    otherZero := ?_ }⟩
  · rw [hcoord]
    exact hza
  · intro u hu hug
    have hu' : u ∈ s(g, w) := by simpa [heval] using hu
    rcases (Sym2.mem_iff.mp hu') with rfl | rfl
    · exact (hug rfl).elim
    · exact hwBlockZero
end QEC.Coding.BalancedProduct.LPSTannerExpansion

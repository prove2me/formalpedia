-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.badNonheavy_card_bound_of_upperEdgeMixing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:14:33.672205+00:00
-- url     : https://prove2.me/submissions/08606fd4-f9f9-4578-a470-9374fd5071dc

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_neighborEdgeCount_mono_source
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_nine_typeCount_mul_badNonheavy_card_le_five_edges
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomTwist_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_blockEquiv_apply
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_inNeighbor_eq_sub
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_inNeighbor_outNeighbor
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_badNonheavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_heavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_lightLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_mediumLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_nonheavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_twoSidedLightTypeSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_usableHeavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_usableNonheavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_outNeighbor_eq_add
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_outNeighbor_inNeighbor
import Theorems.Thm_QEC_Coding_FiberBundle_multipleRotation_val
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
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.independentProduct_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomTwist.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.blockEquiv_apply
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.inNeighbor_eq_sub
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.inNeighbor_outNeighbor
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_badNonheavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_heavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_lightLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_mediumLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_nonheavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_twoSidedLightTypeSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_usableHeavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_usableNonheavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.outNeighbor_eq_add
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.outNeighbor_inNeighbor
attribute [local simp] QEC.Coding.FiberBundle.multipleRotation_val
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
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators
namespace QEC.Coding.FiberBundle.TwistGraph
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (hUpper :
      10 * ell *
          neighborEdgeCount twistSample
            (nonheavyLayerSet Delta w) (heavyLayerSet Delta w) ≤
        22 * typeCount *
          (nonheavyLayerSet Delta w).card *
          (heavyLayerSet Delta w).card) :
    4 * (badNonheavyLayerSet Delta twistSample w).card ≤
      5 * (heavyLayerSet Delta w).card := by
  let badCount := (badNonheavyLayerSet Delta twistSample w).card
  let heavyCount := (heavyLayerSet Delta w).card
  let nonheavyCount := (nonheavyLayerSet Delta w).card
  let edges :=
    neighborEdgeCount twistSample
      (nonheavyLayerSet Delta w) (heavyLayerSet Delta w)
  have hBadSubset :
      badNonheavyLayerSet Delta twistSample w ⊆
        nonheavyLayerSet Delta w := by
    intro u hu
    exact ((mem_badNonheavyLayerSet_iff
      Delta twistSample w u).mp hu).1
  have hBadEdges :
      9 * typeCount * badCount ≤ 5 * edges := by
    calc
      _ ≤ 5 *
          neighborEdgeCount twistSample
            (badNonheavyLayerSet Delta twistSample w)
            (heavyLayerSet Delta w) :=
        nine_typeCount_mul_badNonheavy_card_le_five_edges
          Delta twistSample w
      _ ≤ 5 * edges := Nat.mul_le_mul_left 5
        (neighborEdgeCount_mono_source twistSample
          (badNonheavyLayerSet Delta twistSample w)
          (nonheavyLayerSet Delta w)
          (heavyLayerSet Delta w) hBadSubset)
  have hNonheavyCard : nonheavyCount ≤ ell := by
    calc
      nonheavyCount = (nonheavyLayerSet Delta w).card := rfl
      _ ≤ (Finset.univ : Finset (ZMod ell)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = ell := by simp
  have hCombined :
      (10 * typeCount * ell) * (9 * badCount) ≤
        (10 * typeCount * ell) * (11 * heavyCount) := by
    calc
      (10 * typeCount * ell) * (9 * badCount) =
          10 * ell * (9 * typeCount * badCount) := by ring
      _ ≤ 10 * ell * (5 * edges) :=
        Nat.mul_le_mul_left (10 * ell) hBadEdges
      _ = 5 * (10 * ell * edges) := by ring
      _ ≤ 5 *
          (22 * typeCount * nonheavyCount * heavyCount) :=
        Nat.mul_le_mul_left 5 hUpper
      _ = 110 * typeCount * nonheavyCount * heavyCount := by ring
      _ ≤ 110 * typeCount * ell * heavyCount := by
        exact Nat.mul_le_mul_right heavyCount
          (Nat.mul_le_mul_left (110 * typeCount) hNonheavyCard)
      _ = (10 * typeCount * ell) * (11 * heavyCount) := by ring
  have hNine : 9 * badCount ≤ 11 * heavyCount :=
    Nat.le_of_mul_le_mul_left hCombined
      (Nat.mul_pos
        (Nat.mul_pos (by omega)
          (Nat.pos_of_ne_zero (NeZero.ne typeCount)))
        (Nat.pos_of_ne_zero (NeZero.ne ell)))
  change 4 * badCount ≤ 5 * heavyCount
  omega
end QEC.Coding.FiberBundle.TwistGraph

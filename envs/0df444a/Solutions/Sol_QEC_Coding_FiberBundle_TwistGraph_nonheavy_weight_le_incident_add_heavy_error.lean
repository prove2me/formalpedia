-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.nonheavy_weight_le_incident_add_heavy_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:14:00.784781+00:00
-- url     : https://prove2.me/submissions/e72b6515-fecf-4f7e-a1a2-c20c61e408c6

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_lightLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_mediumLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_heavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_nonheavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_usableNonheavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_badNonheavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_twoSidedLightTypeSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_usableHeavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_layerWeight_le_500_mul_incidentViolationCount_of_usableNonheavy
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomTwist_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_blockEquiv_apply
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_inNeighbor_eq_sub
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_inNeighbor_outNeighbor
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


attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_lightLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_mediumLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_heavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_nonheavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_usableNonheavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_badNonheavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_twoSidedLightTypeSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_usableHeavyLayerSet_iff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators
namespace QEC.Coding.FiberBundle.TwistGraph
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (hLight : HasHHO20LightChecks Delta baseSample twistSample)
    (hBad :
      4 * (badNonheavyLayerSet Delta twistSample w).card ≤
        5 * (heavyLayerSet Delta w).card) :
    Delta *
        (∑ u ∈ nonheavyLayerSet Delta w,
          HammingWeight (layerWord w u)) ≤
      500 *
          (∑ u ∈ nonheavyLayerSet Delta w,
            incidentViolationCount baseSample twistSample w u) +
        5 * (4 * r) * (heavyLayerSet Delta w).card := by
  let usable := usableNonheavyLayerSet Delta twistSample w
  let bad := badNonheavyLayerSet Delta twistSample w
  let nonheavy := nonheavyLayerSet Delta w
  have hUN : usable ⊆ nonheavy := by
    intro u hu
    exact (mem_usableNonheavyLayerSet_iff
      Delta twistSample w u |>.mp hu).1
  have hUB : Disjoint usable bad := by
    refine Finset.disjoint_left.mpr ?_
    intro u hu hbad
    exact (mem_badNonheavyLayerSet_iff
      Delta twistSample w u |>.mp hbad).2 hu
  have hUnion : usable ∪ bad = nonheavy := by
    exact Finset.union_sdiff_of_subset hUN
  have hUsable :
      Delta *
          (∑ u ∈ usable, HammingWeight (layerWord w u)) ≤
        500 *
          (∑ u ∈ nonheavy,
            incidentViolationCount baseSample twistSample w u) := by
    calc
      _ = ∑ u ∈ usable,
          Delta * HammingWeight (layerWord w u) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ u ∈ usable,
          500 * incidentViolationCount baseSample twistSample w u := by
        apply Finset.sum_le_sum
        intro u hu
        exact
          layerWeight_le_500_mul_incidentViolationCount_of_usableNonheavy
            Delta baseSample twistSample w hLight u hu
      _ = 500 *
          (∑ u ∈ usable,
            incidentViolationCount baseSample twistSample w u) := by
        rw [Finset.mul_sum]
      _ ≤ 500 *
          (∑ u ∈ nonheavy,
            incidentViolationCount baseSample twistSample w u) := by
        exact Nat.mul_le_mul_left 500
          (Finset.sum_le_sum_of_subset hUN)
  have hBadWeight :
      Delta * (∑ u ∈ bad, HammingWeight (layerWord w u)) ≤
        5 * (4 * r) * (heavyLayerSet Delta w).card := by
    calc
      _ = ∑ u ∈ bad,
          Delta * HammingWeight (layerWord w u) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ _u ∈ bad, 4 * (4 * r) := by
        apply Finset.sum_le_sum
        intro u hu
        have hun := (mem_badNonheavyLayerSet_iff
          Delta twistSample w u |>.mp hu).1
        exact Nat.le_of_lt
          (mem_nonheavyLayerSet_iff Delta w u |>.mp hun)
      _ = bad.card * (4 * (4 * r)) := by simp
      _ = (4 * bad.card) * (4 * r) := by ring
      _ ≤ (5 * (heavyLayerSet Delta w).card) * (4 * r) :=
        Nat.mul_le_mul_right (4 * r) hBad
      _ = 5 * (4 * r) * (heavyLayerSet Delta w).card := by ring
  change
    Delta *
        (∑ u ∈ nonheavy, HammingWeight (layerWord w u)) ≤
      500 *
          (∑ u ∈ nonheavy,
            incidentViolationCount baseSample twistSample w u) +
        5 * (4 * r) * (heavyLayerSet Delta w).card
  have hWeightSplit :
      (∑ u ∈ nonheavy, HammingWeight (layerWord w u)) =
        (∑ u ∈ usable, HammingWeight (layerWord w u)) +
          ∑ u ∈ bad, HammingWeight (layerWord w u) := by
    rw [← hUnion, Finset.sum_union hUB]
  rw [hWeightSplit, Nat.mul_add]
  exact Nat.add_le_add hUsable hBadWeight
end QEC.Coding.FiberBundle.TwistGraph

-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.hasHHO20LocalTestability_of_partitionedChecks_and_layerMixing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:16:30.380638+00:00
-- url     : https://prove2.me/submissions/d0b71e61-a658-456b-9027-30aed107d007

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_sum_incidentViolationCount_eq_two_mul_violationCount
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_lightLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_mediumLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_heavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_nonheavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_usableNonheavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_badNonheavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_twoSidedLightTypeSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_usableHeavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_sum_hammingWeight_layerWord_le_card_mul_four_r
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_hammingWeight_eq_nonheavy_add_heavy
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_sum_incidentViolationCount_eq_nonheavy_add_heavy
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_two_mul_four_r_mul_medium_card_le_nonheavy_weight
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_nonheavy_weight_le_incident_add_heavy_error
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_four_r_mul_usableHeavy_card_le_heavy_incident
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
    [NeZero r] [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hDelta : 40 ≤ Delta)
    (hChecks :
      HasHHO20PartitionedChecks Delta baseSample twistSample)
    (hMixing : HasHHO20LayerMixing Delta twistSample) :
    HasHHO20LocalTestability Delta baseSample twistSample := by
  intro w hsmall
  let nonheavyWeight :=
    ∑ u ∈ nonheavyLayerSet Delta w,
      HammingWeight (layerWord w u)
  let heavyWeight :=
    ∑ u ∈ heavyLayerSet Delta w,
      HammingWeight (layerWord w u)
  let nonheavyIncident :=
    ∑ u ∈ nonheavyLayerSet Delta w,
      incidentViolationCount baseSample twistSample w u
  let heavyIncident :=
    ∑ u ∈ heavyLayerSet Delta w,
      incidentViolationCount baseSample twistSample w u
  let heavyCount := (heavyLayerSet Delta w).card
  let mediumCount := (mediumLayerSet Delta w).card
  let usableHeavyCount :=
    (usableHeavyLayerSet Delta twistSample w).card
  let n := 4 * r
  let P := Delta * nonheavyWeight
  let Q := n * heavyCount
  have hWeight :
      HammingWeight w = nonheavyWeight + heavyWeight := by
    exact hammingWeight_eq_nonheavy_add_heavy Delta w
  have hIncident :
      nonheavyIncident + heavyIncident =
        2 * violationCount baseSample twistSample w := by
    calc
      _ = ∑ u : ZMod ell,
          incidentViolationCount baseSample twistSample w u := by
        symm
        exact sum_incidentViolationCount_eq_nonheavy_add_heavy
          Delta baseSample twistSample w
      _ = 2 * violationCount baseSample twistSample w :=
        sum_incidentViolationCount_eq_two_mul_violationCount
          baseSample twistSample w
  have hHeavyWeight : heavyWeight ≤ Q := by
    change
      (∑ u ∈ heavyLayerSet Delta w,
        HammingWeight (layerWord w u)) ≤
        (4 * r) * (heavyLayerSet Delta w).card
    calc
      _ ≤ (heavyLayerSet Delta w).card * (4 * r) :=
        sum_hammingWeight_layerWord_le_card_mul_four_r
          w (heavyLayerSet Delta w)
      _ = (4 * r) * (heavyLayerSet Delta w).card := by ring
  have hMedium :
      2 * n * mediumCount ≤ P := by
    exact two_mul_four_r_mul_medium_card_le_nonheavy_weight
      Delta w
  have hMix := hMixing w hsmall
  have hMain : P ≤ 500 * nonheavyIncident + 5 * Q := by
    simpa [P, Q, n, nonheavyWeight, nonheavyIncident, heavyCount,
      Nat.mul_assoc] using
      (nonheavy_weight_le_incident_add_heavy_error
        Delta baseSample twistSample w hChecks.1 hMix.1)
  have hFortyWeight : 40 * nonheavyWeight ≤ P := by
    change 40 * nonheavyWeight ≤ Delta * nonheavyWeight
    exact Nat.mul_le_mul_right nonheavyWeight hDelta
  have hEight :
      8 * (nonheavyWeight + heavyWeight) ≤
        1000 * (nonheavyIncident + heavyIncident) := by
    by_cases hHeavyCase : mediumCount < 1000 * heavyCount
    · have hGoodCount :
          9 * heavyCount ≤ 10 * usableHeavyCount :=
        hMix.2 hHeavyCase
      have hHeavyPay :
          n * usableHeavyCount ≤ 100 * heavyIncident := by
        exact four_r_mul_usableHeavy_card_le_heavy_incident
          Delta baseSample twistSample w hChecks.2
      have hNineQ : 9 * Q ≤ 1000 * heavyIncident := by
        calc
          9 * Q = n * (9 * heavyCount) := by ring
          _ ≤ n * (10 * usableHeavyCount) :=
            Nat.mul_le_mul_left n hGoodCount
          _ = 10 * (n * usableHeavyCount) := by ring
          _ ≤ 10 * (100 * heavyIncident) :=
            Nat.mul_le_mul_left 10 hHeavyPay
          _ = 1000 * heavyIncident := by ring
      have hFortyFiveQ :
          45 * Q ≤ 5000 * heavyIncident := by
        calc
          45 * Q = 5 * (9 * Q) := by ring
          _ ≤ 5 * (1000 * heavyIncident) :=
            Nat.mul_le_mul_left 5 hNineQ
          _ = 5000 * heavyIncident := by ring
      have hFortyHeavy : 40 * heavyWeight ≤ 40 * Q :=
        Nat.mul_le_mul_left 40 hHeavyWeight
      have hScaled :
          40 * (nonheavyWeight + heavyWeight) ≤
            5000 * (nonheavyIncident + heavyIncident) := by
        calc
          40 * (nonheavyWeight + heavyWeight) =
              40 * nonheavyWeight + 40 * heavyWeight := by ring
          _ ≤ P + 40 * Q :=
            Nat.add_le_add hFortyWeight hFortyHeavy
          _ ≤ (500 * nonheavyIncident + 5 * Q) + 40 * Q :=
            Nat.add_le_add_right hMain (40 * Q)
          _ = 500 * nonheavyIncident + 45 * Q := by ring
          _ ≤ 500 * nonheavyIncident + 5000 * heavyIncident :=
            Nat.add_le_add_left hFortyFiveQ (500 * nonheavyIncident)
          _ ≤ 5000 * nonheavyIncident + 5000 * heavyIncident := by
            omega
          _ = 5000 * (nonheavyIncident + heavyIncident) := by ring
      have hmul :
          5 * (8 * (nonheavyWeight + heavyWeight)) ≤
            5 * (1000 * (nonheavyIncident + heavyIncident)) := by
        convert hScaled using 1 <;> ring
      exact Nat.le_of_mul_le_mul_left hmul (by omega)
    · have hLightCase : 1000 * heavyCount ≤ mediumCount := by
        omega
      have hTwoThousandQ : 2000 * Q ≤ P := by
        calc
          2000 * Q = 2 * n * (1000 * heavyCount) := by ring
          _ ≤ 2 * n * mediumCount :=
            Nat.mul_le_mul_left (2 * n) hLightCase
          _ ≤ P := hMedium
      have hTenQ : 10 * Q ≤ P := by
        calc
          10 * Q ≤ 2000 * Q :=
            Nat.mul_le_mul_right Q (by omega)
          _ ≤ P := hTwoThousandQ
      have hP : P ≤ 1000 * nonheavyIncident := by
        omega
      have hThreeTwentyNonheavy :
          320 * nonheavyWeight ≤ 8 * P := by
        calc
          320 * nonheavyWeight = 8 * (40 * nonheavyWeight) := by
            ring
          _ ≤ 8 * P := Nat.mul_le_mul_left 8 hFortyWeight
      have hThreeTwentyHeavy :
          320 * heavyWeight ≤ P := by
        calc
          320 * heavyWeight ≤ 2000 * heavyWeight :=
            Nat.mul_le_mul_right heavyWeight (by omega)
          _ ≤ 2000 * Q :=
            Nat.mul_le_mul_left 2000 hHeavyWeight
          _ ≤ P := hTwoThousandQ
      have hScaled :
          320 * (nonheavyWeight + heavyWeight) ≤
            40000 * (nonheavyIncident + heavyIncident) := by
        calc
          320 * (nonheavyWeight + heavyWeight) =
              320 * nonheavyWeight + 320 * heavyWeight := by ring
          _ ≤ 8 * P + P :=
            Nat.add_le_add hThreeTwentyNonheavy hThreeTwentyHeavy
          _ = 9 * P := by ring
          _ ≤ 9 * (1000 * nonheavyIncident) :=
            Nat.mul_le_mul_left 9 hP
          _ = 9000 * nonheavyIncident := by ring
          _ ≤ 40000 * (nonheavyIncident + heavyIncident) := by
            omega
      have hmul :
          40 * (8 * (nonheavyWeight + heavyWeight)) ≤
            40 * (1000 * (nonheavyIncident + heavyIncident)) := by
        convert hScaled using 1 <;> ring
      exact Nat.le_of_mul_le_mul_left hmul (by omega)
  rw [hWeight]
  have hmul :
      8 * (nonheavyWeight + heavyWeight) ≤
        8 * (250 * violationCount baseSample twistSample w) := by
    calc
      8 * (nonheavyWeight + heavyWeight) ≤
          1000 * (nonheavyIncident + heavyIncident) := hEight
      _ = 1000 *
          (2 * violationCount baseSample twistSample w) := by
        rw [hIncident]
      _ = 8 *
          (250 * violationCount baseSample twistSample w) := by ring
  exact Nat.le_of_mul_le_mul_left hmul (by omega)
end QEC.Coding.FiberBundle.TwistGraph

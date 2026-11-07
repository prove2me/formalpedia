-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.hasHHO20EdgeMixing_of_squaredExpanderMixing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:15:54.094116+00:00
-- url     : https://prove2.me/submissions/78984a50-a227-43f7-93ea-363f71382407

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
import Mathlib.Data.Nat.Dist
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectral
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_complementary_discrepancy_bound
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_heavy_light_discrepancy_bound
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomTwist_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_blockEquiv_apply
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_inNeighbor_eq_sub
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_inNeighbor_outNeighbor
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_badHeavyLayerSet_iff
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
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_badHeavyLayerSet_iff
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
    [NeZero r] [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hSquared : HasHHO20SquaredExpanderMixing twistSample) :
    HasHHO20EdgeMixing Delta twistSample := by
  intro w hHeavySmall hLightLarge
  let nonheavyCount := (nonheavyLayerSet Delta w).card
  let heavyCount := (heavyLayerSet Delta w).card
  let lightCount := (lightLayerSet Delta w).card
  let nonheavyHeavyEdges :=
    neighborEdgeCount twistSample
      (nonheavyLayerSet Delta w) (heavyLayerSet Delta w)
  let heavyLightEdges :=
    neighborEdgeCount twistSample
      (heavyLayerSet Delta w) (lightLayerSet Delta w)
  have hComplement :=
    complementary_discrepancy_bound
      Delta twistSample w hSquared
  have hUpper :
      10 * ell * nonheavyHeavyEdges ≤
        22 * typeCount * nonheavyCount * heavyCount := by
    let expected := 2 * typeCount * nonheavyCount * heavyCount
    let observed := ell * nonheavyHeavyEdges
    let error := Nat.dist observed expected
    have hObserved : observed ≤ expected + error :=
      Nat.dist_tri_right' observed expected
    have hError : 50000 * error ≤ expected := by
      exact hComplement
    have hScaled :
        50000 * observed ≤
          100002 * (typeCount * nonheavyCount * heavyCount) := by
      calc
        50000 * observed ≤ 50000 * (expected + error) :=
          Nat.mul_le_mul_left 50000 hObserved
        _ = 50000 * expected + 50000 * error := by ring
        _ ≤ 50000 * expected + expected :=
          Nat.add_le_add_left hError (50000 * expected)
        _ = 100002 * (typeCount * nonheavyCount * heavyCount) := by
          dsimp only [expected]
          ring
    have hGrouped :
        10 * observed ≤
          22 * (typeCount * nonheavyCount * heavyCount) := by
      omega
    simpa only [observed, Nat.mul_assoc] using hGrouped
  refine ⟨hUpper, ?_⟩
  intro hcase
  have hDeviation :=
    heavy_light_discrepancy_bound
      Delta twistSample w hSquared hcase
  let observed := ell * heavyLightEdges
  let expected := 2 * typeCount * heavyCount * lightCount
  let error := Nat.dist observed expected
  let scale := typeCount * ell * heavyCount
  have hExpected : expected ≤ observed + error :=
    Nat.dist_tri_right observed expected
  have hError : 50000 * error ≤ 64 * scale := by
    simpa only [error, scale, observed, expected, heavyLightEdges,
      heavyCount, lightCount, Nat.mul_assoc] using hDeviation
  have hExpectedScaled :
      50000 * expected ≤ 50000 * observed + 64 * scale := by
    calc
      50000 * expected ≤ 50000 * (observed + error) :=
        Nat.mul_le_mul_left 50000 hExpected
      _ = 50000 * observed + 50000 * error := by ring
      _ ≤ 50000 * observed + 64 * scale :=
        Nat.add_le_add_left hError (50000 * observed)
  have hLightScaled :
      99990 * scale ≤ 50000 * expected := by
    calc
      99990 * scale =
          (10 * typeCount * heavyCount) * (9999 * ell) := by
        dsimp only [scale]
        ring
      _ ≤ (10 * typeCount * heavyCount) * (10000 * lightCount) :=
        Nat.mul_le_mul_left (10 * typeCount * heavyCount) hLightLarge
      _ = 50000 * expected := by
        dsimp only [expected]
        ring
  have hMain :
      99926 * scale ≤ 50000 * observed := by
    omega
  have hTargetScaled :
      (50 * ell) * (1998 * typeCount * heavyCount) ≤
        (50 * ell) * (1000 * heavyLightEdges) := by
    calc
      _ = 99900 * scale := by
        dsimp only [scale]
        ring
      _ ≤ 99926 * scale :=
        Nat.mul_le_mul_right scale (by omega)
      _ ≤ 50000 * observed := hMain
      _ = (50 * ell) * (1000 * heavyLightEdges) := by
        dsimp only [observed]
        ring
  exact Nat.le_of_mul_le_mul_left hTargetScaled
    (Nat.mul_pos (by omega) (Nat.pos_of_ne_zero (NeZero.ne ell)))
end QEC.Coding.FiberBundle.TwistGraph

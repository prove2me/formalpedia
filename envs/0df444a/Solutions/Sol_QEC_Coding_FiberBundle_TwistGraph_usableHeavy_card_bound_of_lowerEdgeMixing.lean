-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.usableHeavy_card_bound_of_lowerEdgeMixing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:16:33.024456+00:00
-- url     : https://prove2.me/submissions/a82a3942-56c1-492f-8781-5b9516fb5f10

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_badHeavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_badHeavy_lightEdges_bound
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_usableHeavy_lightEdges_bound
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


attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_badHeavyLayerSet_iff

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
    (hLower :
      1998 * typeCount * (heavyLayerSet Delta w).card ≤
        1000 *
          neighborEdgeCount twistSample
            (heavyLayerSet Delta w) (lightLayerSet Delta w)) :
    9 * (heavyLayerSet Delta w).card ≤
      10 * (usableHeavyLayerSet Delta twistSample w).card := by
  let good : Finset (ZMod ell) :=
    usableHeavyLayerSet Delta twistSample w
  let bad : Finset (ZMod ell) :=
    badHeavyLayerSet Delta twistSample w
  let heavy : Finset (ZMod ell) := heavyLayerSet Delta w
  let light : Finset (ZMod ell) := lightLayerSet Delta w
  let goodCount : Nat := good.card
  let badCount : Nat := bad.card
  let heavyCount : Nat := heavy.card
  let goodEdges : Nat := neighborEdgeCount twistSample good light
  let badEdges : Nat := neighborEdgeCount twistSample bad light
  let heavyEdges : Nat := neighborEdgeCount twistSample heavy light
  have hGoodSubset : good ⊆ heavy := by
    intro u hu
    exact ((mem_usableHeavyLayerSet_iff
      Delta twistSample w u).mp hu).1
  have hDisjoint : Disjoint good bad := by
    refine Finset.disjoint_left.mpr ?_
    intro u hgood hbad
    exact ((mem_badHeavyLayerSet_iff
      Delta twistSample w u).mp hbad).2 hgood
  have hUnion : good ∪ bad = heavy :=
    Finset.union_sdiff_of_subset hGoodSubset
  have hCard : goodCount + badCount = heavyCount := by
    dsimp only [goodCount, badCount, heavyCount]
    rw [← Finset.card_union_of_disjoint hDisjoint, hUnion]
  have hEdges : goodEdges + badEdges = heavyEdges := by
    dsimp only [goodEdges, badEdges, heavyEdges]
    rw [← hUnion, neighborEdgeCount]
    exact (Finset.sum_union hDisjoint).symm
  have hGoodUpper :
      100 * goodEdges ≤ 200 * typeCount * goodCount := by
    exact usableHeavy_lightEdges_bound Delta twistSample w
  have hBadUpper :
      100 * badEdges + badCount ≤
        198 * typeCount * badCount := by
    exact badHeavy_lightEdges_bound Delta twistSample w
  have hEdgeUpper :
      1000 * heavyEdges + 10 * badCount ≤
        2000 * typeCount * goodCount +
          1980 * typeCount * badCount := by
    calc
      1000 * heavyEdges + 10 * badCount =
          10 *
            ((100 * goodEdges) +
              (100 * badEdges + badCount)) := by
        rw [← hEdges]
        ring
      _ ≤ 10 *
          ((200 * typeCount * goodCount) +
            (198 * typeCount * badCount)) :=
        Nat.mul_le_mul_left 10 (Nat.add_le_add hGoodUpper hBadUpper)
      _ = 2000 * typeCount * goodCount +
          1980 * typeCount * badCount := by ring
  let goodMass := typeCount * goodCount
  let badMass := typeCount * badCount
  let heavyMass := typeCount * heavyCount
  have hMassCard : heavyMass = goodMass + badMass := by
    dsimp only [heavyMass, goodMass, badMass]
    rw [← hCard, Nat.mul_add]
  have hLowerLet :
      1998 * heavyMass ≤ 1000 * heavyEdges := by
    calc
      1998 * heavyMass =
          1998 * typeCount * heavyCount := by
        dsimp only [heavyMass]
        ring
      _ ≤ 1000 * heavyEdges := hLower
  have hEdgeUpperMass :
      1000 * heavyEdges + 10 * badCount ≤
        2000 * goodMass + 1980 * badMass := by
    calc
      _ ≤ 2000 * typeCount * goodCount +
          1980 * typeCount * badCount := hEdgeUpper
      _ = 2000 * goodMass + 1980 * badMass := by
        dsimp only [goodMass, badMass]
        ring
  have hCompareMass :
      1998 * heavyMass + 10 * badCount ≤
        2000 * goodMass + 1980 * badMass := by
    exact
      (Nat.add_le_add_right hLowerLet (10 * badCount)).trans
        hEdgeUpperMass
  have hMass : 18 * badMass ≤ 2 * goodMass := by
    rw [hMassCard] at hCompareMass
    rw [Nat.mul_add] at hCompareMass
    omega
  have hCore :
      (2 * typeCount) * (9 * badCount) ≤
        (2 * typeCount) * goodCount := by
    convert hMass using 1 <;> dsimp [goodMass, badMass] <;> ring
  have hNineBad : 9 * badCount ≤ goodCount :=
    Nat.le_of_mul_le_mul_left hCore
      (Nat.mul_pos (by omega)
        (Nat.pos_of_ne_zero (NeZero.ne typeCount)))
  change 9 * heavyCount ≤ 10 * goodCount
  omega
end QEC.Coding.FiberBundle.TwistGraph

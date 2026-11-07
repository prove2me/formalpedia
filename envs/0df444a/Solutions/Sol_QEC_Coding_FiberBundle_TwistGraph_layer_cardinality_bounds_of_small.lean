-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.layer_cardinality_bounds_of_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:07:05.641211+00:00
-- url     : https://prove2.me/submissions/f49845b0-fb96-4bdf-8595-b03f4ea615bb

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_card_light_add_medium_add_heavy
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomTwist_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_blockEquiv_apply
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_hammingWeight_eq_nonheavy_add_heavy
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_hammingWeight_eq_sum_layerWord
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
    {r ell : Nat}
    [NeZero r] [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (hsmall :
      5000 * Delta * HammingWeight w ≤ ell * (4 * r)) :
    20000 * (heavyLayerSet Delta w).card ≤ ell ∧
      9999 * ell ≤ 10000 * (lightLayerSet Delta w).card := by
  let lightCount := (lightLayerSet Delta w).card
  let mediumCount := (mediumLayerSet Delta w).card
  let heavyCount := (heavyLayerSet Delta w).card
  let n := 4 * r
  have hn : 0 < n := by
    dsimp [n]
    exact Nat.mul_pos (by omega) (Nat.pos_of_ne_zero (NeZero.ne r))
  have hHeavyMass :
      4 * n * heavyCount ≤ Delta * HammingWeight w := by
    calc
      4 * n * heavyCount =
          ∑ _u ∈ heavyLayerSet Delta w, 4 * n := by
        simp [heavyCount, Nat.mul_comm]
      _ ≤ ∑ u ∈ heavyLayerSet Delta w,
          Delta * HammingWeight (layerWord w u) := by
        apply Finset.sum_le_sum
        intro u hu
        simpa [n] using (mem_heavyLayerSet_iff Delta w u).mp hu
      _ = Delta *
          (∑ u ∈ heavyLayerSet Delta w,
            HammingWeight (layerWord w u)) := by
        rw [Finset.mul_sum]
      _ ≤ Delta * HammingWeight w := by
        rw [hammingWeight_eq_nonheavy_add_heavy Delta w]
        exact Nat.mul_le_mul_left Delta (Nat.le_add_left _ _)
  have hHeavyScaled :
      n * (20000 * heavyCount) ≤ n * ell := by
    calc
      n * (20000 * heavyCount) =
          5000 * (4 * n * heavyCount) := by ring
      _ ≤ 5000 * (Delta * HammingWeight w) :=
        Nat.mul_le_mul_left 5000 hHeavyMass
      _ = 5000 * Delta * HammingWeight w := by ring
      _ ≤ ell * (4 * r) := hsmall
      _ = n * ell := by simp [n, Nat.mul_comm]
  have hHeavyCard :
      20000 * heavyCount ≤ ell :=
    Nat.le_of_mul_le_mul_left hHeavyScaled hn
  have hMediumHeavyMass :
      2 * n * (mediumCount + heavyCount) ≤
        Delta * HammingWeight w := by
    have hMH :
        Disjoint (mediumLayerSet Delta w) (heavyLayerSet Delta w) := by
      refine Finset.disjoint_left.mpr ?_
      intro u hu hv
      rw [mem_mediumLayerSet_iff] at hu
      rw [mem_heavyLayerSet_iff] at hv
      omega
    calc
      2 * n * (mediumCount + heavyCount) =
          (∑ _u ∈ mediumLayerSet Delta w, 2 * n) +
            ∑ _u ∈ heavyLayerSet Delta w, 2 * n := by
        rw [Finset.sum_const_nat (fun _ _ => rfl),
          Finset.sum_const_nat (fun _ _ => rfl)]
        dsimp only [mediumCount, heavyCount]
        ring
      _ = ∑ _u ∈ mediumLayerSet Delta w ∪ heavyLayerSet Delta w,
            2 * n := by
        exact (Finset.sum_union hMH).symm
      _ ≤ ∑ u ∈ mediumLayerSet Delta w ∪ heavyLayerSet Delta w,
          Delta * HammingWeight (layerWord w u) := by
        apply Finset.sum_le_sum
        intro u hu
        rw [Finset.mem_union] at hu
        rcases hu with hu | hu
        · exact Nat.le_of_lt
            ((mem_mediumLayerSet_iff Delta w u).mp hu).1
        · have hhu := (mem_heavyLayerSet_iff Delta w u).mp hu
          omega
      _ ≤ ∑ u : ZMod ell,
          Delta * HammingWeight (layerWord w u) := by
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = Delta * HammingWeight w := by
        rw [← Finset.mul_sum, hammingWeight_eq_sum_layerWord]
  have hNonlightScaled :
      n * (10000 * (mediumCount + heavyCount)) ≤ n * ell := by
    calc
      n * (10000 * (mediumCount + heavyCount)) =
          5000 * (2 * n * (mediumCount + heavyCount)) := by ring
      _ ≤ 5000 * (Delta * HammingWeight w) :=
        Nat.mul_le_mul_left 5000 hMediumHeavyMass
      _ = 5000 * Delta * HammingWeight w := by ring
      _ ≤ ell * (4 * r) := hsmall
      _ = n * ell := by simp [n, Nat.mul_comm]
  have hNonlight :
      10000 * (mediumCount + heavyCount) ≤ ell :=
    Nat.le_of_mul_le_mul_left hNonlightScaled hn
  have hPartition :
      lightCount + mediumCount + heavyCount = ell := by
    exact card_light_add_medium_add_heavy Delta w
  refine ⟨?_, ?_⟩
  · exact hHeavyCard
  · omega
end QEC.Coding.FiberBundle.TwistGraph

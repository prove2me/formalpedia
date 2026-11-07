-- Prove2me | solution 1 for QEC.Coding.FiberBundle.horizontalResiduePotential_oneStepSlideCluster_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:23:56.480811+00:00
-- url     : https://prove2.me/submissions/9f3a75b5-9493-4ba5-a82d-21e83abadcfa

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_homologyBaseProjection_add
import Theorems.Thm_QEC_Coding_FiberBundle_weightedHammingCost_add_le
import Theorems.Thm_QEC_Coding_FiberBundle_weightedHammingCost_add_subword_add
import Theorems.Thm_QEC_Coding_FiberBundle_horizontalClusterSubchain_isBinarySubword
import Theorems.Thm_QEC_Coding_FiberBundle_weightedHammingCost_shiftCluster_add_hammingWeight
import Theorems.Thm_QEC_Coding_FiberBundle_horizontalComponent_oneStepSlide
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_groupedDistribution_apply
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
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.columnDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.groupedDistribution_apply
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


attribute [local simp] QEC.Coding.FiberBundle.homologyBaseProjection_add

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (root : Fin (4 * r) × ZMod (ell * ell))
    (hRootSupport : z (Sum.inl root) ≠ 0)
    (hRootResidue : fiberResidue ell root.2 ≠ 0) :
    horizontalResiduePotential
        (oneStepSlide baseSample twistSample z
          (horizontalClusterSubchain
            baseSample twistSample z root)) <
      horizontalResiduePotential z := by
  let h := horizontalClusterSubchain
    baseSample twistSample z root
  let weight := fun bi : Fin (4 * r) × ZMod (ell * ell) =>
    (-fiberResidue ell bi.2).val
  have hSubword : IsBinarySubword h (horizontalComponent z) :=
    horizontalClusterSubchain_isBinarySubword
      baseSample twistSample z root
  have hRootCluster : InSameSupportedHorizontalCluster
      baseSample twistSample z root root :=
    Relation.ReflTransGen.refl
  have hRootEq : h root = z (Sum.inl root) := by
    simp [h, horizontalClusterSubchain, hRootCluster]
  have hNonzero : h ≠ 0 := by
    intro hzero
    apply hRootSupport
    rw [← hRootEq, hzero]
    rfl
  have hWeightPos : 0 < HammingWeight h := by
    exact Nat.pos_of_ne_zero
      ((HammingWeight_eq_zero_iff h).not.mpr hNonzero)
  have hAdd :
      WeightedHammingCost weight
          ((horizontalComponent z + h) +
            shiftHorizontalSubchain (ell * ell) h) ≤
        WeightedHammingCost weight (horizontalComponent z + h) +
          WeightedHammingCost weight
            (shiftHorizontalSubchain (ell * ell) h) :=
    weightedHammingCost_add_le weight
      (horizontalComponent z + h)
      (shiftHorizontalSubchain (ell * ell) h)
  have hPartition :
      WeightedHammingCost weight (horizontalComponent z + h) +
          WeightedHammingCost weight h =
        WeightedHammingCost weight (horizontalComponent z) :=
    weightedHammingCost_add_subword_add
      weight h (horizontalComponent z) hSubword
  have hShift :
      WeightedHammingCost weight
          (shiftHorizontalSubchain (ell * ell) h) +
        HammingWeight h =
      WeightedHammingCost weight h := by
    exact weightedHammingCost_shiftCluster_add_hammingWeight
      baseSample twistSample z root hRootResidue
  rw [horizontalResiduePotential,
    horizontalComponent_oneStepSlide]
  change
    WeightedHammingCost weight
        ((horizontalComponent z + h) +
          shiftHorizontalSubchain (ell * ell) h) <
      WeightedHammingCost weight (horizontalComponent z)
  omega
end QEC.Coding.FiberBundle

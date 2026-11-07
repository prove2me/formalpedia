-- Prove2me | solution 1 for QEC.Coding.FiberBundle.horizontalChainBoundary_cluster_eq_horizontalComponent_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:07:30.782779+00:00
-- url     : https://prove2.me/submissions/1ca55a69-4a5b-49ba-b8cd-66f6c3958cd3

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_homologyBaseProjection_add
import Theorems.Thm_QEC_Coding_FiberBundle_inSameSupportedHorizontalCluster_of_clusterSubchain_ne_zero
import Theorems.Thm_QEC_Coding_FiberBundle_inSameSupportedHorizontalCluster_tail
import Theorems.Thm_QEC_Coding_FiberBundle_mem_horizontalBoundaryShadow_iff
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
attribute [local simp] QEC.Coding.FiberBundle.mem_horizontalBoundaryShadow_iff

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
    (a : Fin (3 * r)) (j : ZMod (ell * ell))
    (hg :
      horizontalChainBoundary baseSample twistSample
        (horizontalClusterSubchain
          baseSample twistSample z root) a j ≠ 0) :
    horizontalChainBoundary baseSample twistSample
        (horizontalClusterSubchain
          baseSample twistSample z root) a j =
      horizontalChainBoundary baseSample twistSample
        (horizontalComponent z) a j := by
  classical
  let D := RandomTwist.fiberBundleData baseSample twistSample
  let h := horizontalClusterSubchain
    baseSample twistSample z root
  have hSum :
      (∑ b : Fin (4 * r),
        RandomBase.boundary baseSample a b *
          h (b, ((D.connection b a).onOne.symm) j)) ≠ 0 := by
    simpa [horizontalChainBoundary, h, D] using hg
  obtain ⟨b₀, _hb₀Mem, hb₀Term⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hSum
  let x : Fin (4 * r) × ZMod (ell * ell) :=
    (b₀, ((D.connection b₀ a).onOne.symm) j)
  have hb₀Boundary :
      RandomBase.boundary baseSample a b₀ ≠ 0 := by
    intro hb₀
    apply hb₀Term
    simp [hb₀]
  have hxSubchain : h x ≠ 0 := by
    intro hx
    apply hb₀Term
    simp [x, hx]
  have hxCluster : InSameSupportedHorizontalCluster
      baseSample twistSample z root x :=
    inSameSupportedHorizontalCluster_of_clusterSubchain_ne_zero
      baseSample twistSample z root x hxSubchain
  have hxEq : h x = z (Sum.inl x) := by
    simp [h, horizontalClusterSubchain, hxCluster]
  have hxSupport : z (Sum.inl x) ≠ 0 := by
    rw [← hxEq]
    exact hxSubchain
  simp only [horizontalChainBoundary]
  apply Finset.sum_congr rfl
  intro b _hbMem
  by_cases hbBoundary :
      RandomBase.boundary baseSample a b = 0
  · simp [hbBoundary]
  let y : Fin (4 * r) × ZMod (ell * ell) :=
    (b, ((D.connection b a).onOne.symm) j)
  by_cases hySupport : z (Sum.inl y) = 0
  · have hySubchain : h y = 0 := by
      simp [h, horizontalClusterSubchain, hySupport]
    change RandomBase.boundary baseSample a b * h y =
      RandomBase.boundary baseSample a b * horizontalComponent z y
    rw [hySubchain]
    have hyHorizontal : horizontalComponent z y = 0 := by
      simpa [horizontalComponent] using hySupport
    rw [hyHorizontal]
  have hxy : HorizontalBoundaryOverlap
      baseSample twistSample x y := by
    refine ⟨a, hb₀Boundary, hbBoundary, ?_⟩
    simp [x, y, D, RandomTwist.fiberBundleData,
      multipleRotationCycleData, cycleData, cycleRotationAutomorphism]
  have hyCluster : InSameSupportedHorizontalCluster
      baseSample twistSample z root y :=
    inSameSupportedHorizontalCluster_tail
      baseSample twistSample z root x y
      hxCluster hxSupport hySupport hxy
  have hyEq : h y = z (Sum.inl y) := by
    simp [h, horizontalClusterSubchain, hyCluster]
  change RandomBase.boundary baseSample a b * h y =
    RandomBase.boundary baseSample a b * horizontalComponent z y
  rw [hyEq]
  rfl
end QEC.Coding.FiberBundle

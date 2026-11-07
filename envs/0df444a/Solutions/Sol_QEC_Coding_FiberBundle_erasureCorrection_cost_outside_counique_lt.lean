-- Prove2me | solution 1 for QEC.Coding.FiberBundle.erasureCorrection_cost_outside_counique_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:30:06.037983+00:00
-- url     : https://prove2.me/submissions/4a6ab7d7-5d7a-45c3-a9f2-5e08c9c774dc

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_horizontalFiber_bundleCoboundary_eraseC0FiberCorrection
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_groupedDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomTwist_distribution_apply
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
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (S : Finset (Fin (3 * r))) (a : Fin (3 * r))
    (ha : a ∈ c0Shadow u)
    (hCounique :
      4 * RandomBase.checkDegree baseSample a <
        5 * RandomBase.couniqueDegree baseSample S a) :
    let C :=
      (RandomBase.couniqueNeighbors baseSample S).filter
        fun b => baseSample (a, b)
    (∑ b ∈ (Finset.univ \ C),
        HammingWeight
          (horizontalFiber
            (bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample)
              (eraseC0FiberCorrection u a)) b)) <
      C.card * HammingWeight (c0Fiber u a) := by
  classical
  let C :=
    (RandomBase.couniqueNeighbors baseSample S).filter
      fun b => baseSample (a, b)
  let N := (Finset.univ : Finset (Fin (4 * r))).filter
    fun b => baseSample (a, b)
  have hCsubsetN : C ⊆ N := by
    intro b hb
    have hbEdge := (Finset.mem_filter.mp hb).2
    simp [N, hbEdge]
  have hfilter :
      (Finset.univ \ C).filter (fun b => baseSample (a, b)) = N \ C := by
    ext b
    simp [N, and_comm]
  have hCcard :
      C.card = RandomBase.couniqueDegree baseSample S a := by
    rfl
  have hNcard : N.card = RandomBase.checkDegree baseSample a := by
    rfl
  have hwPos : 0 < HammingWeight (c0Fiber u a) := by
    have hne : c0Fiber u a ≠ 0 := by
      simpa [c0Shadow] using ha
    have : HammingWeight (c0Fiber u a) ≠ 0 := by
      intro hzero
      exact hne ((HammingWeight_eq_zero_iff (c0Fiber u a)).mp hzero)
    omega
  simp_rw [
    hammingWeight_horizontalFiber_bundleCoboundary_eraseC0FiberCorrection]
  rw [← Finset.sum_filter, hfilter]
  calc
    (∑ _b ∈ N \ C, HammingWeight (c0Fiber u a)) =
        (N \ C).card * HammingWeight (c0Fiber u a) := by simp
    _ = (RandomBase.checkDegree baseSample a -
      RandomBase.couniqueDegree baseSample S a) *
        HammingWeight (c0Fiber u a) := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hCsubsetN,
        hNcard, hCcard]
    _ < RandomBase.couniqueDegree baseSample S a *
        HammingWeight (c0Fiber u a) := by
      exact (Nat.mul_lt_mul_right hwPos).2 (by omega)
    _ = C.card * HammingWeight (c0Fiber u a) := by rw [hCcard]
end QEC.Coding.FiberBundle

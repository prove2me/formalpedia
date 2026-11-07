-- Prove2me | solution 1 for QEC.Coding.FiberBundle.sum_verticalFibers_mul_baseBoundary_eq_zero_of_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:37:15.157225+00:00
-- url     : https://prove2.me/submissions/07f5f6ed-10fb-4bad-9401-1187fca45ea0

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_bundleCocoboundary_apply_eq_horizontal_add_vertical
import Theorems.Thm_QEC_Coding_FiberBundle_mem_middleCocycleCode_iff_bundleCocoboundary_eq_zero
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_groupedDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomTwist_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_multipleRotation_val
import Theorems.Thm_QEC_Coding_FiberBundle_sum_cycleFiberCoboundary_eq_zero
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
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCocycleCode.carrier)
    (b : Fin (4 * r)) :
    (∑ a : Fin (3 * r),
      (∑ j : ZMod (ell * ell), verticalFiber z a j) *
        RandomBase.boundary baseSample a b) = 0 := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  have hzZero : bundleCocoboundary D z = 0 :=
    (mem_middleCocycleCode_iff_bundleCocoboundary_eq_zero D z).mp hz
  have hEquation (j : ZMod (ell * ell)) :
      (∑ i : ZMod (ell * ell),
        z (Sum.inl (b, i)) * cycleBoundary (ell * ell) i j) +
      ∑ a : Fin (3 * r),
        z (Sum.inr (a, (D.connection b a).onOne j)) *
          RandomBase.boundary baseSample a b = 0 := by
    have hj := congrFun hzZero (b, j)
    rw [bundleCocoboundary_apply_eq_horizontal_add_vertical] at hj
    exact hj
  have hSummed :
      (∑ j : ZMod (ell * ell),
        ∑ i : ZMod (ell * ell),
          z (Sum.inl (b, i)) * cycleBoundary (ell * ell) i j) +
      (∑ j : ZMod (ell * ell),
        ∑ a : Fin (3 * r),
          z (Sum.inr (a, (D.connection b a).onOne j)) *
            RandomBase.boundary baseSample a b) = 0 := by
    rw [← Finset.sum_add_distrib]
    simp only [hEquation, Finset.sum_const_zero]
  have hEll : 2 ≤ ell := by
    have hPred : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
    omega
  have hCycle : 2 ≤ ell * ell := by nlinarith
  have hHorizontal :
      (∑ j : ZMod (ell * ell),
        ∑ i : ZMod (ell * ell),
          z (Sum.inl (b, i)) * cycleBoundary (ell * ell) i j) = 0 := by
    exact sum_cycleFiberCoboundary_eq_zero
      (ell * ell) hCycle (horizontalFiber z b)
  rw [hHorizontal, zero_add] at hSummed
  calc
    (∑ a : Fin (3 * r),
        (∑ j : ZMod (ell * ell), verticalFiber z a j) *
          RandomBase.boundary baseSample a b) =
      ∑ j : ZMod (ell * ell),
        ∑ a : Fin (3 * r),
          z (Sum.inr (a, (D.connection b a).onOne j)) *
            RandomBase.boundary baseSample a b := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_mul]
      apply Fintype.sum_equiv (D.connection b a).onOne.symm
      intro j
      simp [verticalFiber]
    _ = 0 := hSummed
end QEC.Coding.FiberBundle

-- Prove2me | solution 1 for QEC.Coding.FiberBundle.oneStepSlide_horizontalComponent_eq_translateBundleWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:53:35.576496+00:00
-- url     : https://prove2.me/submissions/68938f9f-5171-4db6-a55f-a7c947ec01f1

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_homologyBaseProjection_add
import Theorems.Thm_QEC_Coding_FiberBundle_boundary1_apply_eq_horizontal_add_vertical
import Theorems.Thm_QEC_Coding_FiberBundle_cycleFiberChainBoundary_apply
import Theorems.Thm_QEC_Coding_FiberBundle_horizontalFiber_boundary2_oneStepSlideTwoChain
import Theorems.Thm_QEC_Coding_FiberBundle_verticalFiber_boundary2_oneStepSlideTwoChain
import Theorems.Thm_QEC_Coding_FiberBundle_mem_horizontalBoundaryShadow_iff
import Theorems.Thm_QEC_Coding_FiberBundle_translateBundleWord_apply_inl
import Theorems.Thm_QEC_Coding_FiberBundle_translateBundleWord_apply_inr
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
attribute [local simp] QEC.Coding.FiberBundle.translateBundleWord_apply_inl
attribute [local simp] QEC.Coding.FiberBundle.translateBundleWord_apply_inr

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
        ).middleCycleCode.carrier) :
    oneStepSlide baseSample twistSample z (horizontalComponent z) =
      translateBundleWord (ell * ell) 1 z := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  have hzZero : boundary1 D z = 0 :=
    ((chainComplex D).mem_middleCycleCode_iff z).1 hz
  funext q
  rcases q with ⟨b, i⟩ | ⟨a, j⟩
  · rw [translateBundleWord_apply_inl]
    change horizontalFiber
      (oneStepSlide baseSample twistSample z
        (horizontalComponent z)) b i =
      z (Sum.inl (b, i - 1))
    rw [oneStepSlide, show horizontalFiber
        (z +
          boundary2 D (oneStepSlideTwoChain (horizontalComponent z))) b i =
        horizontalFiber z b i +
          horizontalFiber
            (boundary2 D
              (oneStepSlideTwoChain (horizontalComponent z))) b i by rfl]
    rw [horizontalFiber_boundary2_oneStepSlideTwoChain]
    change z (Sum.inl (b, i)) +
      (z (Sum.inl (b, i)) + z (Sum.inl (b, i - 1))) =
        z (Sum.inl (b, i - 1))
    let w := z (Sum.inl (b, i))
    have hww : w + w = 0 := by
      calc
        w + w = w + (-w) := by rw [ZMod.neg_eq_self_mod_two]
        _ = 0 := add_neg_cancel w
    calc
      z (Sum.inl (b, i)) +
          (z (Sum.inl (b, i)) + z (Sum.inl (b, i - 1))) =
        (w + w) + z (Sum.inl (b, i - 1)) := by
          dsimp [w]
          abel
      _ = z (Sum.inl (b, i - 1)) := by rw [hww, zero_add]
  · rw [translateBundleWord_apply_inr]
    change verticalFiber
      (oneStepSlide baseSample twistSample z
        (horizontalComponent z)) a j =
      z (Sum.inr (a, j - 1))
    have hj := congrFun hzZero (a, j)
    rw [boundary1_apply_eq_horizontal_add_vertical] at hj
    have hVertical :
        (∑ k : ZMod (ell * ell),
          D.fiberBoundary j k * z (Sum.inr (a, k))) =
        z (Sum.inr (a, j)) + z (Sum.inr (a, j - 1)) := by
      change cycleFiberChainBoundary (ell * ell)
        (verticalFiber z a) j =
          verticalFiber z a j + verticalFiber z a (j - 1)
      have hEll : 2 ≤ ell := by
        have hne : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
        omega
      exact cycleFiberChainBoundary_apply
        (ell * ell) (by nlinarith) _ j
    rw [oneStepSlide, show verticalFiber
        (z +
          boundary2 D (oneStepSlideTwoChain (horizontalComponent z))) a j =
        verticalFiber z a j +
          verticalFiber
            (boundary2 D
              (oneStepSlideTwoChain (horizontalComponent z))) a j by rfl]
    rw [verticalFiber_boundary2_oneStepSlideTwoChain]
    have hHorizontal :
        (∑ b : Fin (4 * r),
          RandomBase.boundary baseSample a b *
            horizontalComponent z
              (b, (((D.connection b a).onOne.symm) j))) =
          z (Sum.inr (a, j)) + z (Sum.inr (a, j - 1)) := by
      rw [← hVertical]
      have hj' := hj
      change
        (∑ b : Fin (4 * r),
          D.baseBoundary a b *
            z (Sum.inl
              (b, (((D.connection b a).onZero.symm) j)))) +
        (∑ k : ZMod (ell * ell),
          D.fiberBoundary j k * z (Sum.inr (a, k))) = 0 at hj'
      have hneg :
          (∑ b : Fin (4 * r),
            D.baseBoundary a b *
              z (Sum.inl
                (b, (((D.connection b a).onZero.symm) j)))) =
            -(∑ k : ZMod (ell * ell),
              D.fiberBoundary j k * z (Sum.inr (a, k))) :=
        eq_neg_of_add_eq_zero_left hj'
      rw [show
        (∑ b : Fin (4 * r),
          RandomBase.boundary baseSample a b *
            horizontalComponent z
              (b, (((D.connection b a).onOne.symm) j))) =
        (∑ b : Fin (4 * r),
          D.baseBoundary a b *
            z (Sum.inl
              (b, (((D.connection b a).onZero.symm) j)))) by rfl]
      rw [hneg, ZMod.neg_eq_self_mod_two]
    rw [hHorizontal]
    let w := z (Sum.inr (a, j))
    have hww : w + w = 0 := by
      calc
        w + w = w + (-w) := by rw [ZMod.neg_eq_self_mod_two]
        _ = 0 := add_neg_cancel w
    change w + (w + z (Sum.inr (a, j - 1))) =
      z (Sum.inr (a, j - 1))
    calc
      w + (w + z (Sum.inr (a, j - 1))) =
          (w + w) + z (Sum.inr (a, j - 1)) := by abel
      _ = z (Sum.inr (a, j - 1)) := by rw [hww, zero_add]
end QEC.Coding.FiberBundle

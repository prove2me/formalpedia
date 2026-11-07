-- Prove2me | solution 1 for QEC.Coding.FiberBundle.mem_middleBoundaryCode_of_projection_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:09:35.243198+00:00
-- url     : https://prove2.me/submissions/24eea28c-26cf-4d98-89ff-8da3f4804a58

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_homologyBaseProjection_add
import Theorems.Thm_QEC_Coding_FiberBundle_horizontalFiber_add_primitiveBoundary_eq_zero
import Theorems.Thm_QEC_Coding_FiberBundle_verticalFiber_constant_of_boundary1_eq_zero_of_horizontal_zero
import Theorems.Thm_QEC_Coding_FiberBundle_eq_verticalFundamentalWord_of_horizontal_zero_of_vertical_constant
import Theorems.Thm_QEC_Coding_FiberBundle_exists_boundary2_eq_verticalFundamentalWord_of_fullRowRank
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
    (hRank : RandomBase.HasFullRowRank baseSample)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier)
    (hzProjection : homologyBaseProjection z = 0) :
    z ∈ (chainComplex
      (RandomTwist.fiberBundleData baseSample twistSample)
      ).middleBoundaryCode.carrier := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  let primitive := horizontalFiberPrimitiveTwoChain z
  let cleared := z + boundary2 D primitive
  have hzCycle : boundary1 D z = 0 :=
    ((chainComplex D).mem_middleCycleCode_iff z).1 hz
  have hBoundaryCycle : boundary1 D (boundary2 D primitive) = 0 := by
    have hsquare := congrArg
      (fun f : Word (ZMod 2)
          (C2Index (Fin (4 * r)) (ZMod (ell * ell))) →ₗ[ZMod 2]
          Word (ZMod 2)
            (C0Index (Fin (3 * r)) (ZMod (ell * ell))) =>
        f primitive)
      (boundary_squared D)
    simpa using hsquare
  have hClearedCycle : boundary1 D cleared = 0 := by
    change boundary1 D (z + boundary2 D primitive) = 0
    rw [map_add, hzCycle, hBoundaryCycle, add_zero]
  have hClearedHorizontal :
      ∀ b : Fin (4 * r), horizontalFiber cleared b = 0 := by
    intro b
    change horizontalFiber
      (z +
        boundary2
          (RandomTwist.fiberBundleData baseSample twistSample)
          (horizontalFiberPrimitiveTwoChain z)) b = 0
    exact horizontalFiber_add_primitiveBoundary_eq_zero
      baseSample twistSample z hzProjection b
  have hClearedVertical :
      ∀ a : Fin (3 * r), ∀ j,
        verticalFiber cleared a j = verticalFiber cleared a 0 := by
    intro a
    exact verticalFiber_constant_of_boundary1_eq_zero_of_horizontal_zero
      baseSample twistSample cleared hClearedCycle hClearedHorizontal a
  have hClearedForm :
      cleared =
        verticalFundamentalWord
          (baseOne := Fin (4 * r))
          (fiberZero := ZMod (ell * ell))
          (fiberOne := ZMod (ell * ell))
          (verticalFundamentalCoefficient cleared) :=
    eq_verticalFundamentalWord_of_horizontal_zero_of_vertical_constant
      cleared hClearedHorizontal hClearedVertical
  rcases exists_boundary2_eq_verticalFundamentalWord_of_fullRowRank
      baseSample twistSample hRank
      (verticalFundamentalCoefficient cleared) with ⟨c, hc⟩
  have hcCleared : boundary2 D c = cleared := by
    calc
      boundary2 D c =
          verticalFundamentalWord
            (baseOne := Fin (4 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell))
            (verticalFundamentalCoefficient cleared) := by
              simpa [D] using hc
      _ = cleared := hClearedForm.symm
  apply ((chainComplex D).mem_middleBoundaryCode_iff z).2
  refine ⟨primitive + c, ?_⟩
  change boundary2 D (primitive + c) = z
  rw [map_add, hcCleared]
  change boundary2 D primitive + (z + boundary2 D primitive) = z
  funext q
  let w := boundary2 D primitive q
  change w + (z q + w) = z q
  have hww : w + w = 0 := by
    calc
      w + w = w + (-w) := by rw [ZMod.neg_eq_self_mod_two]
      _ = 0 := add_neg_cancel w
  calc
    w + (z q + w) = z q + (w + w) := by abel
    _ = z q := by rw [hww, add_zero]
end QEC.Coding.FiberBundle

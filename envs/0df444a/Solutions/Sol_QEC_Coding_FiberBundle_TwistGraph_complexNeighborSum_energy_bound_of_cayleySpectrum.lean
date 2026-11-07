-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.complexNeighborSum_energy_bound_of_cayleySpectrum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:17:26.925432+00:00
-- url     : https://prove2.me/submissions/ccd1d398-5516-47f8-b401-fd96f20e6f4f

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphOperator
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_dft_complexNeighborSum
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_conj_stdAddChar_neg
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_sum_normSq_dft
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


attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.conj_stdAddChar_neg

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod
namespace QEC.Coding.FiberBundle.TwistGraph
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hSpectrum : HasHHO20CayleySpectrum twistSample)
    (g : ZMod ell → Complex)
    (hzero : (∑ u : ZMod ell, g u) = 0) :
    (50000 : Real) ^ 2 *
        (∑ u : ZMod ell,
          Complex.normSq (complexNeighborSum twistSample g u)) ≤
      (2 * typeCount : Real) ^ 2 *
        ∑ u : ZMod ell, Complex.normSq (g u) := by
  have hPointwise (frequency : ZMod ell) :
      (50000 : Real) ^ 2 *
          Complex.normSq
            (ZMod.dft (complexNeighborSum twistSample g) frequency) ≤
        (2 * typeCount : Real) ^ 2 *
          Complex.normSq (ZMod.dft g frequency) := by
    rw [dft_complexNeighborSum, Complex.normSq_mul]
    by_cases hfrequency : frequency = 0
    · subst frequency
      rw [ZMod.dft_apply_zero, hzero]
      simp
    · have hBound := hSpectrum frequency hfrequency
      have hBoundSq :
          (50000 : Real) ^ 2 *
              Complex.normSq (cayleyMultiplier twistSample frequency) ≤
            (2 * typeCount : Real) ^ 2 := by
        rw [Complex.normSq_eq_norm_sq]
        simpa only [mul_pow] using
          (sq_le_sq₀
            (by positivity :
              (0 : Real) ≤
                50000 * ‖cayleyMultiplier twistSample frequency‖)
            (by positivity : (0 : Real) ≤ 2 * typeCount)).mpr hBound
      calc
        _ =
            ((50000 : Real) ^ 2 *
              Complex.normSq (cayleyMultiplier twistSample frequency)) *
                Complex.normSq (ZMod.dft g frequency) := by ring
        _ ≤
            (2 * typeCount : Real) ^ 2 *
              Complex.normSq (ZMod.dft g frequency) :=
          mul_le_mul_of_nonneg_right hBoundSq
            (Complex.normSq_nonneg _)
  have hSum :
      (∑ frequency : ZMod ell,
        (50000 : Real) ^ 2 *
          Complex.normSq
            (ZMod.dft (complexNeighborSum twistSample g) frequency)) ≤
        ∑ frequency : ZMod ell,
          (2 * typeCount : Real) ^ 2 *
            Complex.normSq (ZMod.dft g frequency) :=
    Finset.sum_le_sum fun frequency _hfrequency =>
      hPointwise frequency
  rw [← Finset.mul_sum, ← Finset.mul_sum,
    sum_normSq_dft, sum_normSq_dft] at hSum
  have hScaled :
      (ell : Real) *
          ((50000 : Real) ^ 2 *
            ∑ u : ZMod ell,
              Complex.normSq (complexNeighborSum twistSample g u)) ≤
        (ell : Real) *
          ((2 * typeCount : Real) ^ 2 *
            ∑ u : ZMod ell, Complex.normSq (g u)) := by
    convert hSum using 1 <;> ring
  have hEll : (0 : Real) < ell := by
    exact_mod_cast NeZero.pos ell
  exact le_of_mul_le_mul_left hScaled hEll
end QEC.Coding.FiberBundle.TwistGraph

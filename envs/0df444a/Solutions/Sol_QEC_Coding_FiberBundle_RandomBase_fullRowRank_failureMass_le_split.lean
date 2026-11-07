-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.fullRowRank_failureMass_le_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:26:25.498037+00:00
-- url     : https://prove2.me/submissions/ec48de99-a9c4-49bd-ba27-2605727439a0

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_groupedDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_subsetRowCombination_zero_eventMass
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_subsetRowCombination_zero_eventMass_small_geometric_le
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_subsetRowCombination_zero_eventMass_large_le
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_sum_nonempty_finset_pow_card
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_fullRowRank_failureMass_le_exact_sum
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
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


attribute [local simp] QEC.Coding.FiberBundle.RandomBase.columnDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.groupedDistribution_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
universe u
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (@HasFullRowRank r) ≤
      (1 + ENNReal.ofReal (Real.exp (-(Delta : Real) / 2))) ^ (3 * r) - 1 +
      (2 : ENNReal) ^ (3 * r) *
        (ENNReal.ofReal ((4 : Real) / 7)) ^ (4 * r) := by
  let t : ENNReal := ENNReal.ofReal (Real.exp (-(Delta : Real) / 2))
  let c : ENNReal := (ENNReal.ofReal ((4 : Real) / 7)) ^ (4 * r)
  calc
    _ ≤
        ∑ A : {A : Finset (Fin (3 * r)) // A.Nonempty},
          (ENNReal.ofReal
            ((1 +
              (1 - 2 * (incidenceProbability (4 * r) Delta).toReal) ^
                A.1.card) / 2)) ^ (4 * r) :=
      fullRowRank_failureMass_le_exact_sum r Delta hDelta
    _ ≤ ∑ A : {A : Finset (Fin (3 * r)) // A.Nonempty},
          (t ^ A.1.card + c) := by
      apply Finset.sum_le_sum
      intro A _
      rw [← subsetRowCombination_zero_eventMass r Delta hDelta A.1]
      by_cases hsmall : A.1.card * Delta ≤ 4 * r
      · exact
          (subsetRowCombination_zero_eventMass_small_geometric_le
            r Delta hr hDelta hHalf A.1 hsmall).trans
            (le_add_right le_rfl)
      · have hlarge : 4 * r ≤ A.1.card * Delta :=
          (Nat.lt_of_not_ge hsmall).le
        exact
          (subsetRowCombination_zero_eventMass_large_le
            r Delta hr hDelta hHalf A.1 hlarge).trans
            (le_add_left le_rfl)
    _ =
        (∑ A : {A : Finset (Fin (3 * r)) // A.Nonempty},
          t ^ A.1.card) +
        ∑ _A : {A : Finset (Fin (3 * r)) // A.Nonempty}, c := by
      exact Finset.sum_add_distrib
    _ ≤
        ((1 + t) ^ (3 * r) - 1) +
          (2 : ENNReal) ^ (3 * r) * c := by
      gcongr
      · simpa only [Fintype.card_fin] using
          (sum_nonempty_finset_pow_card
            (α := Fin (3 * r)) t).le
      · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        gcongr
        norm_cast
        simpa [Fintype.card_finset] using
          (Fintype.card_subtype_le
            (fun A : Finset (Fin (3 * r)) => A.Nonempty))
    _ = _ := rfl
end QEC.Coding.FiberBundle.RandomBase

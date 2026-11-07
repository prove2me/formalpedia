-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.nineteen_twentieths_pow_mul_smallNeighborhood_eventMass_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:15:30.318582+00:00
-- url     : https://prove2.me/submissions/55fe9ec2-b9cc-41be-97b1-330f6f3ed456

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_coe_one_sub_pow_le_ofReal_exp_neg
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_card_mul_incidenceProbability_le_of_small
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_nineteen_twentieths_pow_mul_smallNeighborhood_eventMass_le
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_check_expected_degree
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_groupedDistribution_apply
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
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.columnDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.groupedDistribution_apply
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



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r)
    (cutoff : Nat) :
    ((19 : ENNReal) / 20) ^ cutoff *
        eventMass
          (distribution r Delta hDelta)
          (fun sample =>
            (checkSetNeighborhood sample S).card ≤ cutoff) ≤
      ENNReal.ofReal
        (Real.exp
          (-((399997 : Real) * Delta * S.card / 8000000))) := by
  let load : NNReal :=
    (S.card : NNReal) * incidenceProbability (4 * r) Delta
  let penalty : NNReal :=
    (1 : NNReal) / 20 * ((399997 : NNReal) / 400000 * load)
  have hload :=
    card_mul_incidenceProbability_le_of_small r Delta hr S hSmall
  have honeTwentieth : (1 : NNReal) / 20 ≤ 1 := by
    apply div_le_one_of_le₀
    · norm_num
    · exact bot_le
  have hcoefficient : (399997 : NNReal) / 400000 ≤ 1 := by
    apply div_le_one_of_le₀
    · norm_num
    · exact bot_le
  have hthree : (3 : NNReal) / 400000 ≤ 1 := by
    apply div_le_one_of_le₀
    · norm_num
    · exact bot_le
  have hpenalty : penalty ≤ 1 := by
    calc
      penalty ≤ 1 * (1 * load) := by
        dsimp [penalty]
        gcongr
      _ = load := by simp
      _ ≤ (3 : NNReal) / 400000 := hload
      _ ≤ 1 := hthree
  calc
    _ ≤ (((1 - penalty : NNReal) : ENNReal) ^ (4 * r)) := by
      simpa only [penalty, load] using
        nineteen_twentieths_pow_mul_smallNeighborhood_eventMass_le
          r Delta hr hDelta S hSmall cutoff
    _ ≤ ENNReal.ofReal
        (Real.exp (-((4 * r : Nat) : Real) * (penalty : Real))) :=
      coe_one_sub_pow_le_ofReal_exp_neg penalty hpenalty (4 * r)
    _ = ENNReal.ofReal
        (Real.exp
          (-((399997 : Real) * Delta * S.card / 8000000))) := by
      congr 2
      have hExpected :=
        check_expected_degree r Delta hr
      dsimp [penalty, load]
      norm_num [Nat.cast_mul] at hExpected ⊢
      nlinarith
end QEC.Coding.FiberBundle.RandomBase

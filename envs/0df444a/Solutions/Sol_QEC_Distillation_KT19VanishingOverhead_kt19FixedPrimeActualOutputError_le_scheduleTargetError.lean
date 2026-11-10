-- Prove2me | solution 1 for QEC.Distillation.KT19VanishingOverhead.kt19FixedPrimeActualOutputError_le_scheduleTargetError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:16:30.077211+00:00
-- url     : https://prove2.me/submissions/0da55092-c9e5-4ef1-ad04-6022daac1a94

import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_VanishingOverhead
import Theorems.Thm_QEC_Distillation_KT19VanishingOverhead_kt19SelectedPortErrorRate_eq_outputPortError
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Distillation_DependentBatch_transposeRouting_apply
import Theorems.Thm_QEC_Distillation_DependentBatch_transposeRouting_childInputSlot
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_kt19Routing_apply
import Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_outputWorstPortError_le_smallErrorRecurrence
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_binaryDistillationRun_successProbability
import Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_zero
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_neg
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.KT19ReedSolomon.mem_reedSolomonCode
attribute [local simp] QEC.Distillation.DependentBatch.transposeRouting_apply
attribute [local simp] QEC.Distillation.DependentBatch.transposeRouting_childInputSlot
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Distillation.KT19Protocol.KT19DistillationFamily.kt19Routing_apply
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.binaryDistillationRun_successProbability
attribute [local simp] QEC.Semantics.FiniteInstrument.branchOperator_zero
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg


section
noncomputable section
namespace QEC.Distillation.KT19VanishingOverhead
open Semantics
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open QEC.Distillation.KT19PrimeQuditCSS
open QEC.Distillation.KT19Protocol
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
open Filter Topology
open scoped BigOperators
attribute [local instance]
  QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
attribute [local instance] QEC.Distillation.KT19VanishingOverhead.instKT19VanishingOverheadClassicalDecidable
universe u
variable {p l k : Nat} [NeZero p] [Fact p.Prime]
private theorem kt19FixedPrimeSuccessorError_le_smallErrorRecurrence
    (family : KT19DistillationFamily p l k)
    (distribution : KT19FixedPrimeDistribution p) (port : Fin k)
    (hsmall : ((p - k : Nat) : ℝ) * kt19ErrorRate distribution.mass ≤ 1 / 2) :
    kt19ErrorRate
      (kt19FixedPrimeSuccessorDistribution family distribution port).mass ≤
      KT19DistillationFamily.smallErrorRecurrenceConstant family *
        kt19ErrorRate distribution.mass ^ (l + 1 - k) := by
  change kt19ErrorRate
      (kt19SelectedPortLabelDistribution family distribution.mass
        distribution.mass_nonneg distribution.mass_sum port) ≤ _
  rw [kt19SelectedPortErrorRate_eq_outputPortError family distribution.mass
    distribution.mass_nonneg distribution.mass_sum port]
  letI : Nonempty (Fin k) := KT19DistillationFamily.outputPort_nonempty family
  calc
    kt19OutputPortError
        (family.run distribution.mass distribution.mass_nonneg
          distribution.mass_sum).acceptedOutput port ≤
        KT19DistillationFamily.outputWorstPortError family distribution.mass
          distribution.mass_nonneg distribution.mass_sum :=
      kt19OutputPortError_le_worst _ _
    _ ≤ KT19DistillationFamily.smallErrorRecurrenceConstant family *
          kt19ErrorRate distribution.mass ^ (l + 1 - k) :=
      KT19DistillationFamily.outputWorstPortError_le_smallErrorRecurrence family
        distribution.mass distribution.mass_nonneg distribution.mass_sum hsmall
private theorem kt19FixedPrimeSuccessorError_le_distanceRecurrence
    (family : KT19DistillationFamily p l k)
    (distribution : KT19FixedPrimeDistribution p) (port : Fin k)
    (hsmall : ((p - k : Nat) : ℝ) * kt19ErrorRate distribution.mass ≤ 1 / 2) :
    kt19ErrorRate
      (kt19FixedPrimeSuccessorDistribution family distribution port).mass ≤
      KT19DistillationFamily.smallErrorRecurrenceConstant family *
        kt19ErrorRate distribution.mass ^ (l - k) := by
  have hkl : k ≤ l := family.admissible.2.2.1
  have herr_nonneg : 0 ≤ kt19ErrorRate distribution.mass :=
    kt19ErrorRate_nonneg distribution.mass distribution.mass_nonneg
      distribution.mass_sum
  have herr_le_one : kt19ErrorRate distribution.mass ≤ 1 :=
    kt19ErrorRate_le_one distribution.mass distribution.mass_nonneg
  have hpower : kt19ErrorRate distribution.mass ^ (l + 1 - k) ≤
      kt19ErrorRate distribution.mass ^ (l - k) := by
    calc
      kt19ErrorRate distribution.mass ^ (l + 1 - k) =
          kt19ErrorRate distribution.mass ^ (l - k) *
            kt19ErrorRate distribution.mass := by
              rw [show l + 1 - k = (l - k) + 1 by omega, pow_succ]
      _ ≤ kt19ErrorRate distribution.mass ^ (l - k) * 1 :=
        mul_le_mul_of_nonneg_left herr_le_one
          (pow_nonneg herr_nonneg _)
      _ = kt19ErrorRate distribution.mass ^ (l - k) := by ring
  have hconstant_nonneg :
      0 ≤ KT19DistillationFamily.smallErrorRecurrenceConstant family := by
    unfold KT19DistillationFamily.smallErrorRecurrenceConstant
    positivity
  calc
    kt19ErrorRate
        (kt19FixedPrimeSuccessorDistribution family distribution port).mass ≤
        KT19DistillationFamily.smallErrorRecurrenceConstant family *
          kt19ErrorRate distribution.mass ^ (l + 1 - k) :=
      kt19FixedPrimeSuccessorError_le_smallErrorRecurrence family distribution port
        hsmall
    _ ≤ KT19DistillationFamily.smallErrorRecurrenceConstant family *
          kt19ErrorRate distribution.mass ^ (l - k) :=
      mul_le_mul_of_nonneg_left hpower hconstant_nonneg
private theorem kt19FixedPrime_four_mul_inputCount_le_iterationScale
    (family : KT19DistillationFamily p l k) :
    4 * ((p - k : Nat) : ℝ) ≤ kt19FixedPrimeIterationScale family := by
  unfold kt19FixedPrimeIterationScale
  have hcount_nonneg : (0 : ℝ) ≤ ((p - k : Nat) : ℝ) := Nat.cast_nonneg _
  nlinarith [kt19FixedPrimeRecurrenceConstant_nonneg family, hcount_nonneg]
private theorem kt19FixedPrimeRecurrenceConstant_le_scale_pow_pred
    (family : KT19DistillationFamily p l k) (hdistance : 2 ≤ l - k) :
    KT19DistillationFamily.smallErrorRecurrenceConstant family ≤
      kt19FixedPrimeIterationScale family ^ (l - k - 1) := by
  have hpred : 1 ≤ l - k - 1 := by omega
  calc
    KT19DistillationFamily.smallErrorRecurrenceConstant family ≤
        kt19FixedPrimeIterationScale family := by
      unfold kt19FixedPrimeIterationScale
      have hcount_nonneg : (0 : ℝ) ≤ ((p - k : Nat) : ℝ) := Nat.cast_nonneg _
      nlinarith [hcount_nonneg]
    _ = kt19FixedPrimeIterationScale family ^ 1 := by simp
    _ ≤ kt19FixedPrimeIterationScale family ^ (l - k - 1) :=
      pow_le_pow_right₀ (kt19FixedPrimeIterationScale_one_le family) hpred
private theorem kt19FixedPrimeErrorEnvelope_closed_form
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (depth : Nat) :
    kt19FixedPrimeIterationScale family *
        kt19FixedPrimeErrorEnvelope family initial depth =
      (kt19FixedPrimeIterationScale family * kt19ErrorRate initial.mass) ^
        ((l - k) ^ depth) := by
  have hdistance_one : 1 ≤ l - k := hdistance.trans' (by omega)
  induction depth with
  | zero =>
      simp [kt19FixedPrimeErrorEnvelope]
  | succ depth ih =>
      calc
        kt19FixedPrimeIterationScale family *
            kt19FixedPrimeErrorEnvelope family initial (depth + 1) =
            (kt19FixedPrimeIterationScale family *
              kt19FixedPrimeErrorEnvelope family initial depth) ^ (l - k) := by
          simp only [kt19FixedPrimeErrorEnvelope]
          rw [mul_pow]
          have hsub : l - k - 1 + 1 = l - k :=
            Nat.sub_add_cancel hdistance_one
          calc
            kt19FixedPrimeIterationScale family *
                (kt19FixedPrimeIterationScale family ^ (l - k - 1) *
                  kt19FixedPrimeErrorEnvelope family initial depth ^ (l - k)) =
                (kt19FixedPrimeIterationScale family ^ (l - k - 1) *
                  kt19FixedPrimeIterationScale family) *
                  kt19FixedPrimeErrorEnvelope family initial depth ^ (l - k) := by
                    ring
            _ = kt19FixedPrimeIterationScale family ^ (l - k) *
                  kt19FixedPrimeErrorEnvelope family initial depth ^ (l - k) := by
                    rw [← pow_succ, hsub]
        _ = ((kt19FixedPrimeIterationScale family *
            kt19ErrorRate initial.mass) ^ ((l - k) ^ depth)) ^ (l - k) := by
              rw [ih]
        _ = (kt19FixedPrimeIterationScale family * kt19ErrorRate initial.mass) ^
            ((l - k) ^ (depth + 1)) := by
              rw [← pow_mul, pow_succ]
private theorem kt19FixedPrimeErrorEnvelope_nonneg
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat) :
    0 ≤ kt19FixedPrimeErrorEnvelope family initial depth := by
  induction depth with
  | zero =>
      exact kt19ErrorRate_nonneg initial.mass initial.mass_nonneg initial.mass_sum
  | succ depth ih =>
      simp only [kt19FixedPrimeErrorEnvelope]
      exact mul_nonneg
        (pow_nonneg (kt19FixedPrimeIterationScale_pos family).le _)
        (pow_nonneg ih _)
private theorem kt19FixedPrimeErrorEnvelope_scaled_small
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeInitialSmallDomain family initial) (depth : Nat) :
    kt19FixedPrimeIterationScale family *
      kt19FixedPrimeErrorEnvelope family initial depth ≤ 1 / 4 := by
  rw [kt19FixedPrimeErrorEnvelope_closed_form family initial hdistance]
  have hbase_nonneg : 0 ≤
      kt19FixedPrimeIterationScale family * kt19ErrorRate initial.mass :=
    mul_nonneg (kt19FixedPrimeIterationScale_pos family).le
      (kt19ErrorRate_nonneg initial.mass initial.mass_nonneg initial.mass_sum)
  have hpower : 1 ≤ (l - k) ^ depth :=
    one_le_pow₀ (hdistance.trans' (by omega))
  calc
    (kt19FixedPrimeIterationScale family * kt19ErrorRate initial.mass) ^
        ((l - k) ^ depth) ≤ (1 / 4 : ℝ) ^ ((l - k) ^ depth) :=
      pow_le_pow_left₀ hbase_nonneg hsmall _
    _ ≤ (1 / 4 : ℝ) ^ 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hpower
    _ = 1 / 4 := by norm_num
private theorem kt19FixedPrimePathError_le_errorEnvelope
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeInitialSmallDomain family initial) :
    ∀ (depth : Nat) (path : kt19FixedPrimeOutputSlots k depth),
      kt19FixedPrimePathError family initial depth path ≤
        kt19FixedPrimeErrorEnvelope family initial depth := by
  intro depth
  induction depth with
  | zero =>
      intro path
      simp [kt19FixedPrimePathError, kt19FixedPrimePathDistribution,
        kt19FixedPrimeErrorEnvelope]
  | succ depth ih =>
      intro path
      let priorPath := kt19FixedPrimeOutputPathInit k depth path
      let port := kt19FixedPrimeOutputPathLast k depth path
      let prior := kt19FixedPrimePathDistribution family initial depth priorPath
      have hprior : kt19ErrorRate prior.mass ≤
          kt19FixedPrimeErrorEnvelope family initial depth := by
        simpa [prior, priorPath, kt19FixedPrimePathError] using ih priorPath
      have hscaled : kt19FixedPrimeIterationScale family *
          kt19ErrorRate prior.mass ≤ 1 / 4 := by
        calc
          kt19FixedPrimeIterationScale family * kt19ErrorRate prior.mass ≤
              kt19FixedPrimeIterationScale family *
                kt19FixedPrimeErrorEnvelope family initial depth :=
            mul_le_mul_of_nonneg_left hprior
              (kt19FixedPrimeIterationScale_pos family).le
          _ ≤ 1 / 4 :=
            kt19FixedPrimeErrorEnvelope_scaled_small family initial hdistance
              hsmall depth
      have hlocal : ((p - k : Nat) : ℝ) * kt19ErrorRate prior.mass ≤ 1 / 2 := by
        have hcount_scale :=
          kt19FixedPrime_four_mul_inputCount_le_iterationScale family
        have hcount_nonneg : 0 ≤ kt19ErrorRate prior.mass :=
          kt19ErrorRate_nonneg prior.mass prior.mass_nonneg prior.mass_sum
        have hmult : (4 * ((p - k : Nat) : ℝ)) * kt19ErrorRate prior.mass ≤
            kt19FixedPrimeIterationScale family * kt19ErrorRate prior.mass :=
          mul_le_mul_of_nonneg_right hcount_scale hcount_nonneg
        nlinarith
      have hrecurrence :=
        kt19FixedPrimeSuccessorError_le_distanceRecurrence family prior port hlocal
      have hcoefficient :=
        kt19FixedPrimeRecurrenceConstant_le_scale_pow_pred family hdistance
      have hprior_nonneg : 0 ≤ kt19ErrorRate prior.mass :=
        kt19ErrorRate_nonneg prior.mass prior.mass_nonneg prior.mass_sum
      change kt19ErrorRate
          (kt19FixedPrimeSuccessorDistribution family
            (kt19FixedPrimePathDistribution family initial depth
              (kt19FixedPrimeOutputPathInit k depth path))
            (kt19FixedPrimeOutputPathLast k depth path)).mass ≤ _
      calc
        kt19ErrorRate
            (kt19FixedPrimeSuccessorDistribution family prior port).mass ≤
            KT19DistillationFamily.smallErrorRecurrenceConstant family *
              kt19ErrorRate prior.mass ^ (l - k) := hrecurrence
        _ ≤ kt19FixedPrimeIterationScale family ^ (l - k - 1) *
              kt19ErrorRate prior.mass ^ (l - k) :=
          mul_le_mul_of_nonneg_right hcoefficient
            (pow_nonneg hprior_nonneg _)
        _ ≤ kt19FixedPrimeIterationScale family ^ (l - k - 1) *
              (kt19FixedPrimeErrorEnvelope family initial depth) ^ (l - k) :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hprior_nonneg hprior _)
            (pow_nonneg (kt19FixedPrimeIterationScale_pos family).le _)
        _ = kt19FixedPrimeErrorEnvelope family initial (depth + 1) := rfl
private theorem kt19FixedPrimeReachedOutputError_le_errorEnvelope
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeInitialSmallDomain family initial) (depth : Nat) :
    kt19FixedPrimeReachedOutputError family initial depth ≤
      kt19FixedPrimeErrorEnvelope family initial depth := by
  classical
  unfold kt19FixedPrimeReachedOutputError
  apply Finset.sup'_le
  intro path _
  exact kt19FixedPrimePathError_le_errorEnvelope family initial hdistance hsmall
    depth path
private theorem kt19FixedPrimeScheduleTargetError_eq_scale_mul_errorEnvelope
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (depth : Nat) :
    kt19FixedPrimeScheduleTargetError family initial.mass depth =
      kt19FixedPrimeIterationScale family *
        kt19FixedPrimeErrorEnvelope family initial depth := by
  unfold kt19FixedPrimeScheduleTargetError
  exact (kt19FixedPrimeErrorEnvelope_closed_form family initial hdistance depth).symm
private theorem kt19FixedPrimeReachedOutputError_le_scheduleTargetError
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeInitialSmallDomain family initial) (depth : Nat) :
    kt19FixedPrimeReachedOutputError family initial depth ≤
      kt19FixedPrimeScheduleTargetError family initial.mass depth := by
  calc
    kt19FixedPrimeReachedOutputError family initial depth ≤
        kt19FixedPrimeErrorEnvelope family initial depth :=
      kt19FixedPrimeReachedOutputError_le_errorEnvelope family initial hdistance
        hsmall depth
    _ ≤ kt19FixedPrimeIterationScale family *
          kt19FixedPrimeErrorEnvelope family initial depth := by
      nlinarith [kt19FixedPrimeIterationScale_one_le family,
        kt19FixedPrimeErrorEnvelope_nonneg family initial depth]
    _ = kt19FixedPrimeScheduleTargetError family initial.mass depth :=
      (kt19FixedPrimeScheduleTargetError_eq_scale_mul_errorEnvelope family initial
        hdistance depth).symm
end QEC.Distillation.KT19VanishingOverhead
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19VanishingOverhead
open Semantics
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open QEC.Distillation.KT19PrimeQuditCSS
open QEC.Distillation.KT19Protocol
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
open Filter Topology
open scoped BigOperators
attribute [local instance]
  QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
attribute [local instance] QEC.Distillation.KT19VanishingOverhead.instKT19VanishingOverheadClassicalDecidable
attribute [local instance] QEC.Distillation.KT19VanishingOverhead.instKT19VanishingOverheadClassicalDecidable
universe u
variable {p l k : Nat} [NeZero p] [Fact p.Prime]
namespace QEC.Distillation.KT19VanishingOverhead
theorem _root_.solution
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeIterationScale family * kt19ErrorRate mu ≤ 1 / 4)
    (depth : Nat) :
    kt19FixedPrimeActualOutputError family mu hmu_nonneg hmu_sum depth ≤
      kt19FixedPrimeScheduleTargetError family mu depth := by
  let initial := kt19FixedPrimeInitialDistribution mu hmu_nonneg hmu_sum
  have hsmall_initial : kt19FixedPrimeInitialSmallDomain family initial := by
    exact hsmall
  exact kt19FixedPrimeReachedOutputError_le_scheduleTargetError family initial
    hdistance hsmall_initial depth
end QEC.Distillation.KT19VanishingOverhead

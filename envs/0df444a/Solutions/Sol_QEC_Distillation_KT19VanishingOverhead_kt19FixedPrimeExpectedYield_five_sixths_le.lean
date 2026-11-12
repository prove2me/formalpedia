-- Prove2me | solution 1 for QEC.Distillation.KT19VanishingOverhead.kt19FixedPrimeExpectedYield_five_sixths_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:01:48.480675+00:00
-- url     : https://prove2.me/submissions/67cc490b-802a-4920-82bf-0b966019e45e

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
import Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_kt19Routing_apply
import Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_outputWorstPortError_le_smallErrorRecurrence
import Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_success_ge_one_sub_errorRate_pow
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
private theorem kt19FixedPrimePathStageYield_eq_actualRunSuccess
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) (stage : Fin depth) :
    (kt19FixedPrimePathStageYield family initial depth path stage : ℝ) =
      (kt19FixedPrimePathStageRun family initial depth path stage).successProbability :=
  rfl
private theorem kt19FixedPrimePathYieldFactor_eq_actualStageSuccessProduct
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) :
    (kt19FixedPrimePathYieldFactor family initial depth path : ℝ) =
      ∏ stage : Fin depth,
        (kt19FixedPrimePathStageRun family initial depth path stage).successProbability := by
  classical
  rw [kt19FixedPrimePathYieldFactor, NNReal.coe_prod]
  apply Finset.prod_congr rfl
  intro stage _
  exact kt19FixedPrimePathStageYield_eq_actualRunSuccess
    family initial depth path stage
private theorem kt19FixedPrimePooledAcceptedOutput_eq_sum
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat) :
    (kt19FixedPrimePooledAcceptedOutput family initial depth : ℝ) =
      ∑ path : kt19FixedPrimeOutputSlots k depth,
        (kt19FixedPrimePathYieldFactor family initial depth path : ℝ) := by
  classical
  rw [kt19FixedPrimePooledAcceptedOutput, NNReal.coe_sum]
private theorem kt19FixedPrimeOutputSlots_card_pos
    (family : KT19DistillationFamily p l k) (depth : Nat) :
    0 < Fintype.card (kt19FixedPrimeOutputSlots k depth) :=
  Fintype.card_pos_iff.mpr (kt19FixedPrimeOutputSlots_nonempty family depth)
private theorem kt19FixedPrimePooledYield_eq_sum_div_card
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat) :
    (kt19FixedPrimePooledYield family initial depth : ℝ) =
      (∑ path : kt19FixedPrimeOutputSlots k depth,
        (kt19FixedPrimePathYieldFactor family initial depth path : ℝ)) /
        Fintype.card (kt19FixedPrimeOutputSlots k depth) := by
  rw [kt19FixedPrimePooledYield, NNReal.coe_div,
    kt19FixedPrimePooledAcceptedOutput_eq_sum]
  rfl
private theorem kt19FixedPrimePathError_nonneg
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) :
    0 ≤ kt19FixedPrimePathError family initial depth path := by
  unfold kt19FixedPrimePathError
  exact kt19ErrorRate_nonneg
    (kt19FixedPrimePathDistribution family initial depth path).mass
    (kt19FixedPrimePathDistribution family initial depth path).mass_nonneg
    (kt19FixedPrimePathDistribution family initial depth path).mass_sum
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
private theorem kt19FixedPrimeErrorEnvelope_succ_le_quarter
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeInitialSmallDomain family initial) (depth : Nat) :
    kt19FixedPrimeErrorEnvelope family initial (depth + 1) ≤
      kt19FixedPrimeErrorEnvelope family initial depth / 4 := by
  have hpred : 1 ≤ l - k - 1 := by omega
  have henvelope_nonneg : 0 ≤ kt19FixedPrimeErrorEnvelope family initial depth :=
    kt19FixedPrimeErrorEnvelope_nonneg family initial depth
  have hpower :
      (kt19FixedPrimeIterationScale family *
        kt19FixedPrimeErrorEnvelope family initial depth) ^ (l - k - 1) ≤ 1 / 4 := by
    calc
      (kt19FixedPrimeIterationScale family *
          kt19FixedPrimeErrorEnvelope family initial depth) ^ (l - k - 1) ≤
          (1 / 4 : ℝ) ^ (l - k - 1) :=
        pow_le_pow_left₀
          (mul_nonneg (kt19FixedPrimeIterationScale_pos family).le
            henvelope_nonneg)
          (kt19FixedPrimeErrorEnvelope_scaled_small family initial hdistance
            hsmall depth) _
      _ ≤ (1 / 4 : ℝ) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hpred
      _ = 1 / 4 := by norm_num
  have hfactor :
      kt19FixedPrimeIterationScale family ^ (l - k - 1) *
          kt19FixedPrimeErrorEnvelope family initial depth ^ (l - k) =
        kt19FixedPrimeErrorEnvelope family initial depth *
          (kt19FixedPrimeIterationScale family *
            kt19FixedPrimeErrorEnvelope family initial depth) ^ (l - k - 1) := by
    rw [mul_pow]
    have hsub : l - k - 1 + 1 = l - k :=
      Nat.sub_add_cancel (by omega)
    calc
      kt19FixedPrimeIterationScale family ^ (l - k - 1) *
          kt19FixedPrimeErrorEnvelope family initial depth ^ (l - k) =
          kt19FixedPrimeIterationScale family ^ (l - k - 1) *
            kt19FixedPrimeErrorEnvelope family initial depth ^ (l - k - 1 + 1) := by
              rw [hsub]
      _ = kt19FixedPrimeIterationScale family ^ (l - k - 1) *
            (kt19FixedPrimeErrorEnvelope family initial depth ^ (l - k - 1) *
              kt19FixedPrimeErrorEnvelope family initial depth) := by
              rw [pow_succ]
      _ = kt19FixedPrimeErrorEnvelope family initial depth *
            (kt19FixedPrimeIterationScale family ^ (l - k - 1) *
              kt19FixedPrimeErrorEnvelope family initial depth ^ (l - k - 1)) := by
              ring
  calc
    kt19FixedPrimeErrorEnvelope family initial (depth + 1) =
        kt19FixedPrimeIterationScale family ^ (l - k - 1) *
          kt19FixedPrimeErrorEnvelope family initial depth ^ (l - k) := rfl
    _ = kt19FixedPrimeErrorEnvelope family initial depth *
          (kt19FixedPrimeIterationScale family *
            kt19FixedPrimeErrorEnvelope family initial depth) ^ (l - k - 1) := hfactor
    _ ≤ kt19FixedPrimeErrorEnvelope family initial depth * (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hpower henvelope_nonneg
    _ = kt19FixedPrimeErrorEnvelope family initial depth / 4 := by ring
private theorem kt19FixedPrimeErrorEnvelope_sum_with_tail_le
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeInitialSmallDomain family initial) (depth : Nat) :
    (∑ stage : Fin depth, kt19FixedPrimeErrorEnvelope family initial stage.1) +
      (4 / 3 : ℝ) * kt19FixedPrimeErrorEnvelope family initial depth ≤
        (4 / 3 : ℝ) * kt19ErrorRate initial.mass := by
  induction depth with
  | zero =>
      change 0 + (4 / 3 : ℝ) * kt19ErrorRate initial.mass ≤
        (4 / 3 : ℝ) * kt19ErrorRate initial.mass
      linarith
  | succ depth ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      have hnext := kt19FixedPrimeErrorEnvelope_succ_le_quarter family initial
        hdistance hsmall depth
      nlinarith
private theorem kt19FixedPrimeErrorEnvelope_sum_le
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeInitialSmallDomain family initial) (depth : Nat) :
    ∑ stage : Fin depth, kt19FixedPrimeErrorEnvelope family initial stage.1 ≤
      (4 / 3 : ℝ) * kt19ErrorRate initial.mass := by
  calc
    ∑ stage : Fin depth, kt19FixedPrimeErrorEnvelope family initial stage.1 ≤
        (∑ stage : Fin depth, kt19FixedPrimeErrorEnvelope family initial stage.1) +
          (4 / 3 : ℝ) * kt19FixedPrimeErrorEnvelope family initial depth := by
      exact le_add_of_nonneg_right
        (mul_nonneg (by norm_num)
          (kt19FixedPrimeErrorEnvelope_nonneg family initial depth))
    _ ≤ (4 / 3 : ℝ) * kt19ErrorRate initial.mass :=
      kt19FixedPrimeErrorEnvelope_sum_with_tail_le family initial hdistance hsmall depth
private theorem kt19FixedPrimeInputCount_mul_envelope_sum_le_one_sixth
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeInitialSmallDomain family initial) (depth : Nat) :
    ((p - k : Nat) : ℝ) *
      (∑ stage : Fin depth, kt19FixedPrimeErrorEnvelope family initial stage.1) ≤
        1 / 6 := by
  have hcount_nonneg : 0 ≤ ((p - k : Nat) : ℝ) := Nat.cast_nonneg _
  have hcount_scale :=
    kt19FixedPrime_four_mul_inputCount_le_iterationScale family
  have hscaled_product :
      (4 * ((p - k : Nat) : ℝ)) * kt19ErrorRate initial.mass ≤
        kt19FixedPrimeIterationScale family * kt19ErrorRate initial.mass :=
    mul_le_mul_of_nonneg_right hcount_scale
      (kt19ErrorRate_nonneg initial.mass initial.mass_nonneg initial.mass_sum)
  have hcount_error : ((p - k : Nat) : ℝ) * kt19ErrorRate initial.mass ≤ 1 / 16 := by
    change kt19FixedPrimeIterationScale family * kt19ErrorRate initial.mass ≤ 1 / 4 at hsmall
    nlinarith [hscaled_product, hsmall]
  calc
    ((p - k : Nat) : ℝ) *
        (∑ stage : Fin depth, kt19FixedPrimeErrorEnvelope family initial stage.1) ≤
        ((p - k : Nat) : ℝ) * ((4 / 3 : ℝ) * kt19ErrorRate initial.mass) :=
      mul_le_mul_of_nonneg_left
        (kt19FixedPrimeErrorEnvelope_sum_le family initial hdistance hsmall depth)
        hcount_nonneg
    _ = (4 / 3 : ℝ) * (((p - k : Nat) : ℝ) * kt19ErrorRate initial.mass) := by
      ring
    _ ≤ (4 / 3 : ℝ) * (1 / 16 : ℝ) :=
      mul_le_mul_of_nonneg_left hcount_error (by norm_num)
    _ ≤ 1 / 6 := by norm_num
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
private theorem kt19FixedPrimePathStageError_le_errorEnvelope
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeInitialSmallDomain family initial) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) (stage : Fin depth) :
    kt19FixedPrimePathError family initial stage.1
      (kt19FixedPrimePathStagePath k depth path stage) ≤
        kt19FixedPrimeErrorEnvelope family initial stage.1 :=
  kt19FixedPrimePathError_le_errorEnvelope family initial hdistance hsmall
    stage.1 (kt19FixedPrimePathStagePath k depth path stage)
private theorem kt19FixedPrimePathStageRun_success_one_sub_inputCount_error_le
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) (stage : Fin depth) :
    1 - ((p - k : Nat) : ℝ) *
      kt19FixedPrimePathError family initial stage.1
        (kt19FixedPrimePathStagePath k depth path stage) ≤
      (kt19FixedPrimePathStageRun family initial depth path stage).successProbability := by
  let distribution := kt19FixedPrimePathDistribution family initial stage.1
    (kt19FixedPrimePathStagePath k depth path stage)
  change 1 - ((p - k : Nat) : ℝ) * kt19ErrorRate distribution.mass ≤
    (family.run distribution.mass distribution.mass_nonneg
      distribution.mass_sum).successProbability
  rw [KT19DistillationFamily.run, kt19Run_successProbability]
  change 1 - ((p - k : Nat) : ℝ) * kt19ErrorRate distribution.mass ≤
    kt19Success family.rowFamily distribution.mass distribution.mass_nonneg
      distribution.mass_sum
  have herr_nonneg : 0 ≤ kt19ErrorRate distribution.mass :=
    kt19ErrorRate_nonneg distribution.mass distribution.mass_nonneg
      distribution.mass_sum
  have herr_le_one : kt19ErrorRate distribution.mass ≤ 1 :=
    kt19ErrorRate_le_one distribution.mass distribution.mass_nonneg
  calc
    1 - ((p - k : Nat) : ℝ) * kt19ErrorRate distribution.mass ≤
        (1 - kt19ErrorRate distribution.mass) ^ (p - k) := by
      have hbernoulli := one_add_mul_sub_le_pow
        (a := 1 - kt19ErrorRate distribution.mass) (by linarith) (p - k)
      convert hbernoulli using 1 <;> first | rfl | ring
    _ ≤ kt19Success family.rowFamily distribution.mass distribution.mass_nonneg
          distribution.mass_sum :=
      KT19DistillationFamily.success_ge_one_sub_errorRate_pow family
        distribution.mass distribution.mass_nonneg distribution.mass_sum
private theorem kt19FixedPrimeFiniteOneSubSum_le_product {ι : Type*}
    (s : Finset ι) (loss : ι → ℝ)
    (hloss_nonneg : ∀ item ∈ s, 0 ≤ loss item)
    (hloss_le_one : ∀ item ∈ s, loss item ≤ 1) :
    1 - ∑ item ∈ s, loss item ≤ ∏ item ∈ s, (1 - loss item) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert item s hitem ih =>
      rw [Finset.sum_insert hitem, Finset.prod_insert hitem]
      have hsum_nonneg : 0 ≤ ∑ other ∈ s, loss other :=
        Finset.sum_nonneg fun other hother =>
          hloss_nonneg other (Finset.mem_insert_of_mem hother)
      have hrest : 1 - ∑ item ∈ s, loss item ≤
          ∏ item ∈ s, (1 - loss item) :=
        ih (fun other hother => hloss_nonneg other
          (Finset.mem_insert_of_mem hother))
          (fun other hother => hloss_le_one other
            (Finset.mem_insert_of_mem hother))
      calc
        1 - (loss item + ∑ other ∈ s, loss other) ≤
            (1 - loss item) * (1 - ∑ other ∈ s, loss other) := by
          nlinarith [hloss_nonneg item (Finset.mem_insert_self item s),
            hsum_nonneg]
        _ ≤ (1 - loss item) * ∏ other ∈ s, (1 - loss other) :=
          mul_le_mul_of_nonneg_left hrest
            (by linarith [hloss_le_one item (Finset.mem_insert_self item s)])
private theorem kt19FixedPrimePathLoss_sum_le_one_sixth
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeInitialSmallDomain family initial) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) :
    ∑ stage : Fin depth, ((p - k : Nat) : ℝ) *
      kt19FixedPrimePathError family initial stage.1
        (kt19FixedPrimePathStagePath k depth path stage) ≤ 1 / 6 := by
  rw [← Finset.mul_sum]
  calc
    ((p - k : Nat) : ℝ) *
        ∑ stage : Fin depth,
          kt19FixedPrimePathError family initial stage.1
            (kt19FixedPrimePathStagePath k depth path stage) ≤
        ((p - k : Nat) : ℝ) *
          ∑ stage : Fin depth,
            kt19FixedPrimeErrorEnvelope family initial stage.1 :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun stage _ =>
          kt19FixedPrimePathStageError_le_errorEnvelope family initial hdistance
            hsmall depth path stage)
        (Nat.cast_nonneg _)
    _ ≤ 1 / 6 :=
      kt19FixedPrimeInputCount_mul_envelope_sum_le_one_sixth family initial
        hdistance hsmall depth
private theorem kt19FixedPrimePathYieldFactor_five_sixths_le
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeInitialSmallDomain family initial) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) :
    (5 / 6 : ℝ) ≤ (kt19FixedPrimePathYieldFactor family initial depth path : ℝ) := by
  classical
  let loss : Fin depth → ℝ := fun stage =>
    ((p - k : Nat) : ℝ) *
      kt19FixedPrimePathError family initial stage.1
        (kt19FixedPrimePathStagePath k depth path stage)
  have hloss_nonneg (stage : Fin depth) : 0 ≤ loss stage := by
    dsimp [loss]
    exact mul_nonneg (Nat.cast_nonneg _)
      (kt19FixedPrimePathError_nonneg family initial stage.1
        (kt19FixedPrimePathStagePath k depth path stage))
  have hsum_loss : ∑ stage : Fin depth, loss stage ≤ 1 / 6 := by
    simpa only [loss] using
      kt19FixedPrimePathLoss_sum_le_one_sixth family initial hdistance hsmall
        depth path
  have hloss_le_one (stage : Fin depth) : loss stage ≤ 1 := by
    calc
      loss stage ≤ ∑ other : Fin depth, loss other :=
        Finset.single_le_sum (fun other _ => hloss_nonneg other)
          (Finset.mem_univ stage)
      _ ≤ 1 / 6 := hsum_loss
      _ ≤ 1 := by norm_num
  have hproduct_lower :
      1 - ∑ stage : Fin depth, loss stage ≤
        ∏ stage : Fin depth,
          (kt19FixedPrimePathStageRun family initial depth path stage).successProbability := by
    calc
      1 - ∑ stage : Fin depth, loss stage ≤
          ∏ stage : Fin depth, (1 - loss stage) := by
        simpa using (kt19FixedPrimeFiniteOneSubSum_le_product Finset.univ loss
          (fun stage _ => hloss_nonneg stage)
          (fun stage _ => hloss_le_one stage))
      _ ≤ ∏ stage : Fin depth,
          (kt19FixedPrimePathStageRun family initial depth path stage).successProbability := by
        refine Finset.prod_le_prod ?_ ?_
        · intro stage _
          linarith [hloss_le_one stage]
        · intro stage _
          dsimp [loss]
          exact kt19FixedPrimePathStageRun_success_one_sub_inputCount_error_le
            family initial depth path stage
  rw [kt19FixedPrimePathYieldFactor_eq_actualStageSuccessProduct]
  linarith
private theorem kt19FixedPrimePooledYield_five_sixths_le
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeInitialSmallDomain family initial) (depth : Nat) :
    (5 / 6 : ℝ) ≤ (kt19FixedPrimePooledYield family initial depth : ℝ) := by
  classical
  have hcard : 0 < (Fintype.card (kt19FixedPrimeOutputSlots k depth) : ℝ) := by
    exact_mod_cast kt19FixedPrimeOutputSlots_card_pos family depth
  rw [kt19FixedPrimePooledYield_eq_sum_div_card]
  apply (le_div_iff₀ hcard).mpr
  calc
    (5 / 6 : ℝ) * Fintype.card (kt19FixedPrimeOutputSlots k depth) =
        ∑ path : kt19FixedPrimeOutputSlots k depth, (5 / 6 : ℝ) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
    _ ≤ ∑ path : kt19FixedPrimeOutputSlots k depth,
        (kt19FixedPrimePathYieldFactor family initial depth path : ℝ) :=
      Finset.sum_le_sum fun path _ =>
        kt19FixedPrimePathYieldFactor_five_sixths_le family initial hdistance
          hsmall depth path
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
    (5 / 6 : ℝ) ≤
      (kt19FixedPrimeExpectedYield family mu hmu_nonneg hmu_sum depth : ℝ) := by
  let initial := kt19FixedPrimeInitialDistribution mu hmu_nonneg hmu_sum
  have hsmall_initial : kt19FixedPrimeInitialSmallDomain family initial := by
    exact hsmall
  simpa [kt19FixedPrimeExpectedYield, initial] using
    kt19FixedPrimePooledYield_five_sixths_le family initial hdistance
      hsmall_initial depth
end QEC.Distillation.KT19VanishingOverhead

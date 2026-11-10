-- Prove2me | solution 1 for QEC.Distillation.KT19Protocol.KT19DistillationFamily.outputWorstPortError_le_smallErrorRecurrence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T14:50:00.835199+00:00
-- url     : https://prove2.me/submissions/4de171d0-1151-4095-a6cf-0102d981d497

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_MagicResource
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_P11CubicBridge
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
import Definitions.Def_QEC_Semantics_Instruments_Branches_BranchOperatorLinear
import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_Protocol
import Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_kt19Routing_apply
import Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_success_ge_one_sub_errorRate_pow
import Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_outputWorstPortError_le_two_mul_card_mul_card_errorRate_pow_exactDistance_div_success
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
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
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
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


attribute [local simp] QEC.Distillation.KT19Protocol.KT19DistillationFamily.kt19Routing_apply

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19Protocol
open Semantics
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open QEC.Distillation.KT19PrimeQuditCSS
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
open QEC.Distillation.KT19P11ReedSolomonCubicBridge
attribute [local instance]
  QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
attribute [local instance] QEC.Distillation.KT19Protocol.instKT19ProtocolClassicalDecidable
attribute [local instance] QEC.Distillation.KT19Protocol.instKT19ProtocolClassicalDecidable
universe u
variable (p : Nat) [NeZero p]
variable {Site : Type u} [Fintype Site] [DecidableEq Site]
variable {q : Nat} [NeZero q] [Fact q.Prime]
variable {Logical Stabilizer : Type u} [Fintype Logical] [Fintype Stabilizer]
attribute [local instance] QEC.Distillation.KT19Protocol.p11Prime
attribute [local instance] QEC.Distillation.KT19Protocol.p11NeZero
attribute [local instance] QEC.Distillation.KT19Protocol.p11Prime QEC.Distillation.KT19Protocol.p11NeZero
open QEC.Distillation.KT19Protocol.KT19DistillationFamily
variable {p l k : Nat} [NeZero p] [Fact p.Prime]
namespace QEC.Distillation.KT19Protocol.KT19DistillationFamily
theorem _root_.solution
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1)
    (hsmall : ((p - k : Nat) : ℝ) * kt19ErrorRate mu ≤ 1 / 2) :
    outputWorstPortError family mu hmu_nonneg hmu_sum ≤
      smallErrorRecurrenceConstant family *
        kt19ErrorRate mu ^ (l + 1 - k) := by
  have heps_nonneg : 0 ≤ kt19ErrorRate mu :=
    kt19ErrorRate_nonneg mu hmu_nonneg hmu_sum
  have heps_le_one : kt19ErrorRate mu ≤ 1 :=
    kt19ErrorRate_le_one mu hmu_nonneg
  rcases family.admissible with ⟨_, _, hkl, _, hthree⟩
  have hkp : k < p := by
    have hp5 : 5 ≤ p := family.primeAtLeastFive.five_le
    omega
  have hcount_pos : 0 < p - k := Nat.sub_pos_of_lt hkp
  have hcount_one : (1 : ℝ) ≤ ((p - k : Nat) : ℝ) := by
    exact_mod_cast hcount_pos
  have heps : kt19ErrorRate mu < 1 := by
    by_contra hnot
    have heps_one : 1 ≤ kt19ErrorRate mu := le_of_not_gt hnot
    have hone_le_product :
        (1 : ℝ) ≤ ((p - k : Nat) : ℝ) * kt19ErrorRate mu := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hcount_one)
        (sub_nonneg.mpr heps_one)]
    linarith
  have hbernoulli :
      1 - ((p - k : Nat) : ℝ) * kt19ErrorRate mu ≤
        (1 - kt19ErrorRate mu) ^ (p - k) := by
    calc
      1 - ((p - k : Nat) : ℝ) * kt19ErrorRate mu =
          1 + ((p - k : Nat) : ℝ) *
            ((1 - kt19ErrorRate mu) - 1) := by ring
      _ ≤ (1 - kt19ErrorRate mu) ^ (p - k) :=
        one_add_mul_sub_le_pow (a := 1 - kt19ErrorRate mu) (by linarith) (p - k)
  have hsuccess_half :
      (1 / 2 : ℝ) ≤ kt19Success family.rowFamily mu hmu_nonneg hmu_sum :=
    calc
      (1 / 2 : ℝ) ≤ 1 - ((p - k : Nat) : ℝ) * kt19ErrorRate mu := by
        linarith
      _ ≤ (1 - kt19ErrorRate mu) ^ (p - k) := hbernoulli
      _ ≤ kt19Success family.rowFamily mu hmu_nonneg hmu_sum :=
        success_ge_one_sub_errorRate_pow family mu hmu_nonneg hmu_sum
  have hsuccess_pos :
      0 < kt19Success family.rowFamily mu hmu_nonneg hmu_sum := by
    linarith
  let tail : ℝ :=
    (Fintype.card (Word (ZMod p) (KeptPunctureLocation p k)) : ℝ) *
      kt19ErrorRate mu ^ (l + 1 - k)
  have htail_nonneg : 0 ≤ tail := by
    dsimp only [tail]
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg heps_nonneg _)
  have htail_div :
      tail / kt19Success family.rowFamily mu hmu_nonneg hmu_sum ≤ 2 * tail := by
    rw [div_le_iff₀ hsuccess_pos]
    have hmul := mul_le_mul_of_nonneg_left hsuccess_half htail_nonneg
    nlinarith
  calc
    outputWorstPortError family mu hmu_nonneg hmu_sum ≤
        2 * (Fintype.card (PrimeQuditRegisterLabel p (Fin k)) : ℝ) *
          (tail / kt19Success family.rowFamily mu hmu_nonneg hmu_sum) := by
      simpa only [tail] using
        (outputWorstPortError_le_two_mul_card_mul_card_errorRate_pow_exactDistance_div_success
          family mu hmu_nonneg hmu_sum heps)
    _ ≤ 2 * (Fintype.card (PrimeQuditRegisterLabel p (Fin k)) : ℝ) *
          (2 * tail) :=
      mul_le_mul_of_nonneg_left htail_div
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    _ = smallErrorRecurrenceConstant family *
          kt19ErrorRate mu ^ (l + 1 - k) := by
      simp only [smallErrorRecurrenceConstant, tail]
      ring
end QEC.Distillation.KT19Protocol.KT19DistillationFamily

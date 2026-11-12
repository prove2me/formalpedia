-- Prove2me | solution 1 for QEC.Distillation.KT19VanishingOverhead.kt19ChangingPrimeExponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:34:57.665916+00:00
-- url     : https://prove2.me/submissions/5da548f7-10e0-4851-8f72-a49018a6f86d

import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_VanishingOverhead
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Distillation_DependentBatch_transposeRouting_apply
import Theorems.Thm_QEC_Distillation_DependentBatch_transposeRouting_childInputSlot
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_kt19Routing_apply
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
private theorem kt19ExplicitParameters_eight_ray (t : Nat) :
    kt19ExplicitK (1 + 8 * t) = t ∧
      kt19ExplicitL (1 + 8 * t) = 2 * t ∧
      (1 + 8 * t) - kt19ExplicitK (1 + 8 * t) = 7 * t + 1 ∧
      kt19ExplicitL (1 + 8 * t) - kt19ExplicitK (1 + 8 * t) = t := by
  simp only [kt19ExplicitK, kt19ExplicitL]
  omega
private theorem kt19FixedPrimeGamma_eight_ray_le (t : Nat) (ht : 1 < t) :
    kt19FixedPrimeGamma (1 + 8 * t)
        (kt19ExplicitL (1 + 8 * t)) (kt19ExplicitK (1 + 8 * t)) ≤
      Real.log 8 / Real.log (t : ℝ) := by
  rcases kt19ExplicitParameters_eight_ray t with ⟨hk, hl, hinput, hdistance⟩
  have hinput' : (1 + 8 * t) - t = 7 * t + 1 := by
    simpa only [hk] using hinput
  have hdistance' : 2 * t - t = t := by
    simpa only [hk, hl] using hdistance
  rw [kt19FixedPrimeGamma, hk, hl, hinput', hdistance']
  have htpos_nat : 0 < t := by omega
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast htpos_nat
  have hlogt : 0 < Real.log (t : ℝ) := by
    apply Real.log_pos
    exact_mod_cast ht
  apply (div_le_div_iff_of_pos_right hlogt).2
  apply Real.log_le_log
  · exact div_pos (by positivity) htpos
  · apply (div_le_iff₀ htpos).2
    have htone : (1 : ℝ) ≤ (t : ℝ) := by
      exact_mod_cast (show 1 ≤ t by omega)
    push_cast
    nlinarith
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
theorem _root_.solution (bound : Nat) (eta : ℝ) (heta : 0 < eta) :
    ∃ p : Nat, bound ≤ p ∧ Nat.Prime p ∧ 32 ≤ p ∧ p ≡ 1 [MOD 8] ∧
      kt19FixedPrimeGamma p (kt19ExplicitL p) (kt19ExplicitK p) < eta := by
  obtain ⟨N, hN⟩ := exists_nat_gt
    (max (bound : ℝ) (Real.exp (Real.log 8 / eta) + 4))
  obtain ⟨p, hp, hpgt, hpmod⟩ :=
    Nat.exists_prime_gt_modEq_one (8 * N + 1) (by norm_num : 8 ≠ 0)
  have hNbound_real : (bound : ℝ) < (N : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hN
  have hNbound : bound < N := by exact_mod_cast hNbound_real
  have hNexp : Real.exp (Real.log 8 / eta) + 4 < (N : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hN
  have hNfour_real : (4 : ℝ) < (N : ℝ) := by
    nlinarith [Real.exp_pos (Real.log 8 / eta)]
  have hNfour : 4 < N := by exact_mod_cast hNfour_real
  have hlarge : 32 ≤ p := by omega
  have hptwo : 2 ≤ p := hp.two_le
  have hpone : 1 ≤ p := by omega
  obtain ⟨t, hpt⟩ := (Nat.modEq_iff_exists_eq_add hpone).mp hpmod.symm
  have hNt : N < t := by omega
  have ht : 1 < t := by omega
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
  have htexp : Real.exp (Real.log 8 / eta) < (t : ℝ) := by
    have hNt_real : (N : ℝ) < (t : ℝ) := by exact_mod_cast hNt
    nlinarith
  have hlog_lower : Real.log 8 / eta < Real.log (t : ℝ) :=
    (Real.lt_log_iff_exp_lt htpos).2 htexp
  have hlogt : 0 < Real.log (t : ℝ) := by
    apply Real.log_pos
    exact_mod_cast ht
  have hsmall : Real.log 8 / Real.log (t : ℝ) < eta := by
    apply (div_lt_iff₀ hlogt).2
    have h := (div_lt_iff₀ heta).1 hlog_lower
    simpa [mul_comm] using h
  refine ⟨p, le_trans (Nat.le_of_lt hNbound) (Nat.le_of_lt ?_), hp, hlarge,
    hpmod, ?_⟩
  · omega
  · rw [hpt]
    exact (kt19FixedPrimeGamma_eight_ray_le t ht).trans_lt hsmall
end QEC.Distillation.KT19VanishingOverhead

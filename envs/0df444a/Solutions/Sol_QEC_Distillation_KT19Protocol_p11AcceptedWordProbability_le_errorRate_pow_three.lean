-- Prove2me | solution 1 for QEC.Distillation.KT19Protocol.p11AcceptedWordProbability_le_errorRate_pow_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T14:35:28.118534+00:00
-- url     : https://prove2.me/submissions/651ccce0-e8f7-4f71-948d-39e4d4ac479e

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
import Theorems.Thm_QEC_Distillation_KT19Protocol_p11AcceptedWord_hammingWeight_ge_three
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_mu_nonzero_le
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
section
noncomputable section
namespace QEC.Distillation.KT19Protocol
open Semantics
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open QEC.Distillation.KT19PrimeQuditCSS
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
open QEC.Distillation.KT19P11ReedSolomonCubicBridge
attribute [local instance]
  QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
attribute [local instance] QEC.Distillation.KT19Protocol.instKT19ProtocolClassicalDecidable
universe u
variable (p : Nat) [NeZero p]
variable {Site : Type u} [Fintype Site] [DecidableEq Site]
section Syndromes
variable {q : Nat} [NeZero q] [Fact q.Prime]
variable {Logical Stabilizer : Type u} [Fintype Logical] [Fintype Stabilizer]
namespace KT19DistillationFamily
variable {p l k : Nat} [NeZero p] [Fact p.Prime]
end KT19DistillationFamily
attribute [local instance] QEC.Distillation.KT19Protocol.p11Prime QEC.Distillation.KT19Protocol.p11NeZero
private theorem p11_wordProbability_le_errorRate_pow_hammingWeight
    (mu : ZMod 11 → ℝ) (hmu_nonneg : ∀ a : ZMod 11, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod 11, mu a = 1)
    (error : Word (ZMod 11) (KeptPunctureLocation 11 2)) :
    wordProbability 11 mu error ≤ kt19ErrorRate mu ^ HammingWeight error := by
  classical
  have hmu_zero : mu 0 = 1 - kt19ErrorRate mu := by
    unfold kt19ErrorRate
    ring
  unfold wordProbability
  calc
    (∏ site : KeptPunctureLocation 11 2, mu (error site)) ≤
        ∏ site : KeptPunctureLocation 11 2,
          if error site = 0 then 1 else kt19ErrorRate mu := by
      refine Finset.prod_le_prod ?_ ?_
      · intro site _
        exact hmu_nonneg (error site)
      · intro site _
        by_cases hzero : error site = 0
        · simpa [hzero] using kt19Mu_zero_le_one mu hmu_nonneg hmu_sum
        · simpa [hzero] using
            (mu_nonzero_le (p := 11) mu (kt19ErrorRate mu) hmu_zero
              hmu_nonneg hmu_sum (error site) hzero)
    _ = kt19ErrorRate mu ^ HammingWeight error := by
      rw [Finset.prod_ite]
      have hnonzero :
          (Finset.univ.filter fun site : KeptPunctureLocation 11 2 =>
            ¬ error site = 0) = hammingSupport error := by
        ext site
        simp [hammingSupport]
      have hzero_card :
          (Finset.univ.filter fun site : KeptPunctureLocation 11 2 =>
            error site = 0).card =
              Fintype.card (KeptPunctureLocation 11 2) - HammingWeight error := by
        have hpartition := Finset.card_filter_add_card_filter_not
          (s := Finset.univ)
          (fun site : KeptPunctureLocation 11 2 => error site = 0)
        rw [hnonzero, ← HammingWeight_eq_card_hammingSupport] at hpartition
        have huniv_card :
            (Finset.univ : Finset (KeptPunctureLocation 11 2)).card =
              Fintype.card (KeptPunctureLocation 11 2) := by
          simp
        rw [huniv_card] at hpartition
        exact Nat.eq_sub_of_add_eq hpartition
      have hnonzero_card :
          (Finset.univ.filter fun site : KeptPunctureLocation 11 2 =>
            ¬ error site = 0).card = HammingWeight error := by
        rw [hnonzero, HammingWeight_eq_card_hammingSupport]
      rw [Finset.prod_const, Finset.prod_const, hzero_card, hnonzero_card]
      ring
namespace KT19DistillationFamily
variable {p l k : Nat} [NeZero p] [Fact p.Prime]
end KT19DistillationFamily
end Syndromes
end QEC.Distillation.KT19Protocol
end
end

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
namespace QEC.Distillation.KT19Protocol
theorem _root_.solution
    (mu : ZMod 11 → ℝ) (hmu_nonneg : ∀ a : ZMod 11, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod 11, mu a = 1)
    (error : Word (ZMod 11) (KeptPunctureLocation 11 2))
    (haccepted : kt19AcceptedWord p11CubicRowFamily error) (herror : error ≠ 0) :
    wordProbability 11 mu error ≤ kt19ErrorRate mu ^ 3 := by
  calc
    wordProbability 11 mu error ≤ kt19ErrorRate mu ^ HammingWeight error :=
      p11_wordProbability_le_errorRate_pow_hammingWeight mu hmu_nonneg hmu_sum error
    _ ≤ kt19ErrorRate mu ^ 3 :=
      pow_le_pow_of_le_one
        (kt19ErrorRate_nonneg mu hmu_nonneg hmu_sum)
        (kt19ErrorRate_le_one mu hmu_nonneg)
        (p11AcceptedWord_hammingWeight_ge_three error haccepted herror)
end QEC.Distillation.KT19Protocol

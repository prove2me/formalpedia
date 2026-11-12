-- Prove2me | solution 1 for QEC.Distillation.KT19VanishingOverhead.kt19FixedPrimeSuccessfulOutputCost_le_polylog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:38:15.888846+00:00
-- url     : https://prove2.me/submissions/4eb310d7-24f9-4576-b62b-133c6b6c6885

import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_VanishingOverhead
import Theorems.Thm_QEC_Distillation_KT19VanishingOverhead_kt19FixedPrimeSuccessfulOutputCost_le_six_fifths
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm

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
private theorem kt19FixedPrimeGamma_eq
    (p l k : Nat) :
    kt19FixedPrimeGamma p l k =
      Real.log (((p - k : Nat) : ℝ) / (k : ℝ)) /
        Real.log ((l - k : Nat) : ℝ) :=
  rfl
private theorem kt19FixedPrimeInputCount_pos
    (family : KT19DistillationFamily p l k) : 0 < p - k := by
  rcases family.admissible with ⟨_, hk, hkl, hlp, htriple⟩
  have hp_five : 5 ≤ p := family.primeAtLeastFive.five_le
  omega
private theorem kt19FixedPrimeOutputCount_pos
    (family : KT19DistillationFamily p l k) : 0 < k := by
  have hk : 1 ≤ k := family.admissible.2.1
  omega
private theorem kt19FixedPrime_rpow_distancePow_eq_inputOutputRatio_pow
    (family : KT19DistillationFamily p l k) (hdistance : 2 ≤ l - k)
    (depth : Nat) :
    Real.rpow (((l - k : Nat) : ℝ) ^ depth) (kt19FixedPrimeGamma p l k) =
      ((((p - k : Nat) : ℝ) / (k : ℝ)) ^ depth) := by
  have hdistance_nat : 1 < l - k := by omega
  have hdistance_real : (1 : ℝ) < ((l - k : Nat) : ℝ) := by
    exact_mod_cast hdistance_nat
  have hratio : 0 < ((p - k : Nat) : ℝ) / (k : ℝ) := by
    apply div_pos
    · exact_mod_cast kt19FixedPrimeInputCount_pos family
    · exact_mod_cast kt19FixedPrimeOutputCount_pos family
  calc
    Real.rpow (((l - k : Nat) : ℝ) ^ depth) (kt19FixedPrimeGamma p l k) =
        Real.exp (Real.log (((l - k : Nat) : ℝ) ^ depth) *
          kt19FixedPrimeGamma p l k) := by
          exact Real.rpow_def_of_pos (by positivity) _
    _ = Real.exp ((depth : ℝ) *
        Real.log (((p - k : Nat) : ℝ) / (k : ℝ))) := by
      congr 1
      rw [Real.log_pow]
      rw [kt19FixedPrimeGamma_eq]
      field_simp [ne_of_gt (Real.log_pos hdistance_real)] <;> ring
    _ = Real.rpow (((p - k : Nat) : ℝ) / (k : ℝ)) (depth : ℝ) := by
      symm
      calc
        Real.rpow (((p - k : Nat) : ℝ) / (k : ℝ)) (depth : ℝ) =
            Real.exp (Real.log (((p - k : Nat) : ℝ) / (k : ℝ)) *
              (depth : ℝ)) :=
          Real.rpow_def_of_pos hratio _
        _ = Real.exp ((depth : ℝ) *
            Real.log (((p - k : Nat) : ℝ) / (k : ℝ))) :=
          congrArg Real.exp (mul_comm _ _)
    _ = ((((p - k : Nat) : ℝ) / (k : ℝ)) ^ depth) :=
      Real.rpow_natCast _ _
private theorem kt19FixedPrimeLogGrowthBase_pos
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1)
    (hepsilon : 0 < kt19ErrorRate mu)
    (hsmall : kt19FixedPrimeIterationScale family * kt19ErrorRate mu ≤ 1 / 4) :
    0 < kt19FixedPrimeLogGrowthBase family mu := by
  unfold kt19FixedPrimeLogGrowthBase
  apply neg_pos.mpr
  apply Real.log_neg
  · exact mul_pos (kt19FixedPrimeIterationScale_pos family) hepsilon
  · exact hsmall.trans_lt (by norm_num)
private theorem kt19FixedPrime_distancePow_mul_logGrowthBase_eq_log
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (hepsilon : 0 < kt19ErrorRate mu) (depth : Nat) :
    ((l - k : Nat) : ℝ) ^ depth * kt19FixedPrimeLogGrowthBase family mu =
      Real.log (1 / kt19FixedPrimeScheduleTargetError family mu depth) := by
  have hbase : 0 < kt19FixedPrimeIterationScale family * kt19ErrorRate mu :=
    mul_pos (kt19FixedPrimeIterationScale_pos family) hepsilon
  unfold kt19FixedPrimeScheduleTargetError
  rw [Real.log_div (by norm_num) (ne_of_gt (pow_pos hbase _)), Real.log_one,
    Real.log_pow]
  push_cast
  unfold kt19FixedPrimeLogGrowthBase
  ring
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
    (hepsilon : 0 < kt19ErrorRate mu)
    (hsmall : kt19FixedPrimeIterationScale family * kt19ErrorRate mu ≤ 1 / 4)
    (depth : Nat) :
    kt19FixedPrimeSuccessfulOutputCost family mu hmu_nonneg hmu_sum depth ≤
      kt19FixedPrimeCostCoefficient family mu *
        Real.rpow (Real.log
          (1 / kt19FixedPrimeScheduleTargetError family mu depth))
          (kt19FixedPrimeGamma p l k) := by
  have hbase : 0 < kt19FixedPrimeLogGrowthBase family mu :=
    kt19FixedPrimeLogGrowthBase_pos family mu hmu_nonneg hmu_sum hepsilon hsmall
  have hbase_rpow : 0 < Real.rpow (kt19FixedPrimeLogGrowthBase family mu)
      (kt19FixedPrimeGamma p l k) :=
    Real.rpow_pos_of_pos hbase _
  have hlog := kt19FixedPrime_distancePow_mul_logGrowthBase_eq_log family mu
    hepsilon depth
  have hfactorization :
      Real.rpow (((l - k : Nat) : ℝ) ^ depth *
          kt19FixedPrimeLogGrowthBase family mu) (kt19FixedPrimeGamma p l k) =
        Real.rpow (((l - k : Nat) : ℝ) ^ depth) (kt19FixedPrimeGamma p l k) *
          Real.rpow (kt19FixedPrimeLogGrowthBase family mu)
            (kt19FixedPrimeGamma p l k) :=
    Real.mul_rpow (by positivity) hbase.le
  calc
    kt19FixedPrimeSuccessfulOutputCost family mu hmu_nonneg hmu_sum depth ≤
        (6 / 5 : ℝ) * ((((p - k : Nat) : ℝ) / (k : ℝ)) ^ depth) :=
      kt19FixedPrimeSuccessfulOutputCost_le_six_fifths family mu hmu_nonneg
        hmu_sum hdistance hsmall depth
    _ = (6 / 5 : ℝ) *
        Real.rpow (((l - k : Nat) : ℝ) ^ depth) (kt19FixedPrimeGamma p l k) := by
      rw [kt19FixedPrime_rpow_distancePow_eq_inputOutputRatio_pow family
        hdistance depth]
    _ =
        ((6 / 5 : ℝ) *
          Real.rpow (((l - k : Nat) : ℝ) ^ depth) (kt19FixedPrimeGamma p l k) *
          Real.rpow (kt19FixedPrimeLogGrowthBase family mu)
            (kt19FixedPrimeGamma p l k)) /
          Real.rpow (kt19FixedPrimeLogGrowthBase family mu)
            (kt19FixedPrimeGamma p l k) := by
      field_simp [ne_of_gt hbase_rpow]
    _ = kt19FixedPrimeCostCoefficient family mu *
        Real.rpow (((l - k : Nat) : ℝ) ^ depth *
          kt19FixedPrimeLogGrowthBase family mu) (kt19FixedPrimeGamma p l k) := by
      rw [hfactorization]
      unfold kt19FixedPrimeCostCoefficient
      field_simp [ne_of_gt hbase_rpow]
    _ = kt19FixedPrimeCostCoefficient family mu *
        Real.rpow (Real.log
          (1 / kt19FixedPrimeScheduleTargetError family mu depth))
          (kt19FixedPrimeGamma p l k) := by
      rw [hlog]
end QEC.Distillation.KT19VanishingOverhead

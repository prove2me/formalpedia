-- Prove2me | solution 1 for QEC.Distillation.KT19VanishingOverhead.kt19FixedPrime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:40:59.451016+00:00
-- url     : https://prove2.me/submissions/e691ee19-5016-4fa3-b6e9-074dc3a31674

import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_VanishingOverhead
import Theorems.Thm_QEC_Distillation_KT19VanishingOverhead_kt19FixedPrimeTargetError_tendsto_zero
import Theorems.Thm_QEC_Distillation_KT19VanishingOverhead_kt19FixedPrimeActualOutputError_le_scheduleTargetError
import Theorems.Thm_QEC_Distillation_KT19VanishingOverhead_kt19FixedPrimeActualOutputError_tendsto_zero
import Theorems.Thm_QEC_Distillation_KT19VanishingOverhead_kt19FixedPrimeExpectedYield_pos
import Theorems.Thm_QEC_Distillation_KT19VanishingOverhead_kt19FixedPrimeSuccessfulOutputCost_le_polylog
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
private theorem kt19FixedPrimeCostCoefficient_pos
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1)
    (hepsilon : 0 < kt19ErrorRate mu)
    (hsmall : kt19FixedPrimeIterationScale family * kt19ErrorRate mu ≤ 1 / 4) :
    0 < kt19FixedPrimeCostCoefficient family mu := by
  unfold kt19FixedPrimeCostCoefficient
  exact div_pos (by norm_num)
    (Real.rpow_pos_of_pos
      (kt19FixedPrimeLogGrowthBase_pos family mu hmu_nonneg hmu_sum
        hepsilon hsmall) _)
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
    (hsmall : kt19FixedPrimeIterationScale family * kt19ErrorRate mu ≤ 1 / 4) :
    Tendsto (fun depth : Nat =>
      kt19FixedPrimeScheduleTargetError family mu depth) atTop (𝓝 0) ∧
      Tendsto (fun depth : Nat =>
        kt19FixedPrimeActualOutputError family mu hmu_nonneg hmu_sum depth)
        atTop (𝓝 0) ∧
      DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
        (fun depth => kt19FixedPrimeInputSlots p k depth)
        (fun depth => kt19FixedPrimeOutputSlots k depth)
        (kt19FixedPrimeScheduleTargetError family mu)
        (kt19FixedPrimeActualOutputError family mu hmu_nonneg hmu_sum)
        (kt19FixedPrimeExpectedYield family mu hmu_nonneg hmu_sum)
        (kt19FixedPrimeGamma p l k) (kt19FixedPrimeCostCoefficient family mu) := by
  refine ⟨kt19FixedPrimeTargetError_tendsto_zero family mu hmu_nonneg hmu_sum
      hdistance hepsilon hsmall,
    kt19FixedPrimeActualOutputError_tendsto_zero family mu hmu_nonneg hmu_sum
      hdistance hepsilon hsmall, ?_⟩
  refine ⟨(kt19FixedPrimeCostCoefficient_pos family mu hmu_nonneg hmu_sum
      hepsilon hsmall).le, ?_⟩
  intro depth _ _
  refine ⟨kt19FixedPrimeActualOutputError_le_scheduleTargetError family mu
      hmu_nonneg hmu_sum hdistance hsmall depth,
    kt19FixedPrimeExpectedYield_pos family mu hmu_nonneg hmu_sum hdistance
      hsmall depth, ?_⟩
  exact kt19FixedPrimeSuccessfulOutputCost_le_polylog family mu hmu_nonneg
    hmu_sum hdistance hepsilon hsmall depth
end QEC.Distillation.KT19VanishingOverhead

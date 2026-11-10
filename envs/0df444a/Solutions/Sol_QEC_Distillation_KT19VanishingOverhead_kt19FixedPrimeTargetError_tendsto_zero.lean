-- Prove2me | solution 1 for QEC.Distillation.KT19VanishingOverhead.kt19FixedPrimeTargetError_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:16:27.227984+00:00
-- url     : https://prove2.me/submissions/97bc4768-7f8f-4b39-a32f-b9247ea7ac2f

import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_VanishingOverhead

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
      kt19FixedPrimeScheduleTargetError family mu depth) atTop (𝓝 0) := by
  let initial := kt19FixedPrimeInitialDistribution mu hmu_nonneg hmu_sum
  have hbase_nonneg : 0 ≤
      kt19FixedPrimeIterationScale family * kt19ErrorRate initial.mass :=
    mul_nonneg (kt19FixedPrimeIterationScale_pos family).le
      (kt19ErrorRate_nonneg initial.mass initial.mass_nonneg initial.mass_sum)
  have hbase_lt_one :
      kt19FixedPrimeIterationScale family * kt19ErrorRate initial.mass < 1 := by
    change kt19FixedPrimeIterationScale family * kt19ErrorRate mu ≤ 1 / 4 at hsmall
    exact hsmall.trans_lt (by norm_num : (1 / 4 : ℝ) < 1)
  have hpow : Tendsto (fun exponent : Nat =>
      (kt19FixedPrimeIterationScale family * kt19ErrorRate initial.mass) ^ exponent)
        atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase_nonneg hbase_lt_one
  have hgrowth : Tendsto (fun depth : Nat => (l - k) ^ depth) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by omega)
  exact hpow.comp hgrowth
end QEC.Distillation.KT19VanishingOverhead

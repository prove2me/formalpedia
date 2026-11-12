-- Prove2me | solution 1 for QEC.Distillation.KT19VanishingOverhead.kt19FixedPrimeActualOutputError_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:01:12.554148+00:00
-- url     : https://prove2.me/submissions/1cbbccb4-ffbc-40ae-9de6-f0a7cfc9d0d1

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
private theorem kt19FixedPrimeReachedOutputError_nonneg
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat) :
    0 ≤ kt19FixedPrimeReachedOutputError family initial depth := by
  classical
  unfold kt19FixedPrimeReachedOutputError
  obtain ⟨path, _, hpath⟩ := Finset.exists_mem_eq_sup'
    ⟨(kt19FixedPrimeOutputSlots_nonempty family depth).some, Finset.mem_univ _⟩
    (fun path => kt19FixedPrimePathError family initial depth path)
  rw [hpath]
  exact kt19FixedPrimePathError_nonneg family initial depth path
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
      kt19FixedPrimeActualOutputError family mu hmu_nonneg hmu_sum depth)
      atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds
    (kt19FixedPrimeTargetError_tendsto_zero family mu hmu_nonneg hmu_sum
      hdistance hepsilon hsmall)
    (fun depth => by
      unfold kt19FixedPrimeActualOutputError
      exact kt19FixedPrimeReachedOutputError_nonneg family
        (kt19FixedPrimeInitialDistribution mu hmu_nonneg hmu_sum) depth)
    (fun depth => kt19FixedPrimeActualOutputError_le_scheduleTargetError family mu
      hmu_nonneg hmu_sum hdistance hsmall depth)
end QEC.Distillation.KT19VanishingOverhead

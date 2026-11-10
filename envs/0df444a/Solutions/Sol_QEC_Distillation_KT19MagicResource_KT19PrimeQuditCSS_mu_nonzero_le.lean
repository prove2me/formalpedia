-- Prove2me | solution 1 for QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.mu_nonzero_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:50:46.194994+00:00
-- url     : https://prove2.me/submissions/63f7febc-7cf4-4145-814f-17544c64aecb

import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_MagicResource
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19MagicResource
open Semantics
open QEC.Distillation.KT19PrimeQuditCSS
open scoped BigOperators
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
universe u v w
variable (p : Nat) [NeZero p]
variable {Site : Type u} [Fintype Site]
attribute [local instance] QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS._p2m_local_instance_d135975d44_41
attribute [local instance] QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.primeQuditRegisterLabelFintypeLocal
namespace QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
theorem _root_.solution (mu : ZMod p → ℝ) (eps : ℝ)
    (hmu0 : mu 0 = 1 - eps) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (a : ZMod p) (ha : a ≠ 0) :
    mu a ≤ eps := by
  have hsum0 : (∑ b : ZMod p, if b = 0 then mu 0 else 0) = mu 0 := by simp
  have hsumAll :
      (∑ b : ZMod p, ((if b = 0 then 0 else mu b) + if b = 0 then mu 0 else 0)) =
        ∑ b : ZMod p, mu b := by
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : b = 0 <;> simp [hb]
  have hsum' : (∑ b : ZMod p, if b = 0 then 0 else mu b) + mu 0 =
      ∑ b : ZMod p, mu b := by
    rw [← hsum0, ← Finset.sum_add_distrib, hsumAll]
  have hsum_nonzero : (∑ b : ZMod p, if b = 0 then 0 else mu b) = eps := by
    rw [hmu_sum] at hsum'
    rw [hmu0] at hsum'
    linarith
  have hle : mu a ≤ ∑ b : ZMod p, if b = 0 then 0 else mu b := by
    calc
      mu a = ∑ b : ZMod p, if b = a then (if b = 0 then 0 else mu b) else 0 := by
        simp [ha]
      _ ≤ ∑ b : ZMod p, if b = 0 then 0 else mu b := by
        apply Finset.sum_le_sum
        intro b _
        by_cases hba : b = a
        · by_cases hb : b = 0
          · simp [hba]
          · simp [hba]
        · by_cases hb : b = 0
          · simp [hb]
          · simp [hba, hb, hmu_nonneg b]
  exact hle.trans_eq hsum_nonzero
end QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS

-- Prove2me | solution 1 for QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.sum_magicBasisCharacter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:53:30.935187+00:00
-- url     : https://prove2.me/submissions/51d50d5c-5f67-4c26-834d-8b1f6f7d0769

import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_MagicResource
import Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_sum_phase_smul
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
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
theorem _root_.solution (y x : ZMod p) :
    (∑ a : ZMod p, starRingEnd ℂ (magicBasisAmplitude p a y) * magicBasisAmplitude p a x) =
      if y = x then (p : ℂ) else 0 := by
  rw [Finset.sum_congr rfl (fun a _ => calc
    starRingEnd ℂ (magicBasisAmplitude p a y) * magicBasisAmplitude p a x
        = phase p ((x - y) * a + (x ^ 3 - y ^ 3)) := by
      unfold magicBasisAmplitude
      rw [phase_conj, ← phase_add]
      congr 1
      ring)]
  rw [Finset.sum_congr rfl (fun a _ => by rw [phase_add])]
  rw [← Finset.sum_mul]
  rw [sum_phase_smul]
  by_cases hyx : y = x
  · subst y
    simp
  · have hne : x - y ≠ 0 := by
      intro h
      exact hyx (sub_eq_zero.mp h).symm
    simp [hyx, hne]
end QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS

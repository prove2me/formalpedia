-- Prove2me | solution 1 for QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.sum_phase_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:51:36.915196+00:00
-- url     : https://prove2.me/submissions/501abd12-c78e-43eb-b930-626ad8089c91

import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_MagicResource
import Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_phase_eq_one_iff
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
theorem _root_.solution (c : ZMod p) :
    ∑ x : ZMod p, phase p (c * x) = if c = 0 then (p : ℂ) else 0 := by
  by_cases hc : c = 0
  · subst c
    simp [ZMod.card]
  · let chi : AddChar (ZMod p) ℂ := {
      toFun := fun x => phase p (c * x)
      map_zero_eq_one' := by simp [phase_zero]
      map_add_eq_mul' := by
        intro x y
        rw [mul_add, phase_add]
    }
    have hchi : chi ≠ 1 := by
      intro h
      have h1 := congrArg (fun χ : AddChar (ZMod p) ℂ => χ 1) h
      change phase p (c * 1) = (1 : AddChar (ZMod p) ℂ) 1 at h1
      simp only [mul_one, AddChar.one_apply] at h1
      exact hc ((phase_eq_one_iff p c).1 h1)
    simpa [chi, hc] using AddChar.sum_eq_zero_of_ne_one hchi
end QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS

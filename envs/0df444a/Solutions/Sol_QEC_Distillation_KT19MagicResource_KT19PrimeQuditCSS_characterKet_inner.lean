-- Prove2me | solution 1 for QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.characterKet_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:55:30.968391+00:00
-- url     : https://prove2.me/submissions/0fdc88e9-56ee-42a0-be15-ef5543b0faa0

import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_MagicResource
import Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_sum_register_phase
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
theorem _root_.solution (e f : PrimeQuditRegisterLabel p Site) :
    inner ℂ (characterKet p e) (characterKet p f) = if e = f then 1 else 0 := by
  rw [PiLp.inner_apply]
  have hpoint (x : PrimeQuditRegisterLabel p Site) :
      inner ℂ (characterKet p e x) (characterKet p f x) =
        ((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) *
          ((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) *
            phase p (registerPairing p (f - e) x) := by
    rw [RCLike.inner_apply']
    simp only [characterKet_apply, map_mul, map_pow, map_inv₀, Complex.conj_ofReal, phase_conj]
    rw [mul_mul_mul_comm]
    congr 1
    rw [← phase_add]
    congr 1
    simp [registerPairing, sub_mul, Finset.sum_sub_distrib]
    abel
  rw [Finset.sum_congr rfl (fun x _ => hpoint x)]
  rw [← Finset.mul_sum]
  rw [sum_register_phase p (f - e)]
  by_cases hef : e = f
  · subst f
    simp
    rw [← inv_pow]
    exact registerNorm_sq_mul_pow p
  · have hne : f - e ≠ 0 := by
      intro h
      exact hef (sub_eq_zero.mp h).symm
    simp [hef, hne]
end QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS

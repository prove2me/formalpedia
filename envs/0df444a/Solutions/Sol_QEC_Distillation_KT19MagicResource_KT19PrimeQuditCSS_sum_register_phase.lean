-- Prove2me | solution 1 for QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.sum_register_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:53:24.041319+00:00
-- url     : https://prove2.me/submissions/5a35c9e1-f50e-4687-bd6e-7ec4f30c9e76

import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_MagicResource
import Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_sum_phase_smul
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_phase_finset_sum
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
theorem _root_.solution (f : PrimeQuditRegisterLabel p Site) :
    ∑ x : PrimeQuditRegisterLabel p Site, phase p (registerPairing p f x) =
      if f = 0 then (p : ℂ) ^ Fintype.card Site else 0 := by
  calc
    ∑ x : PrimeQuditRegisterLabel p Site, phase p (registerPairing p f x) =
        ∑ x : PrimeQuditRegisterLabel p Site, ∏ site : Site, phase p (f site * x site) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [registerPairing]
      exact phase_finset_sum p Finset.univ (fun site => f site * x site)
    _ = ∏ site : Site, ∑ a : ZMod p, phase p (f site * a) := by
      rw [labelUniv_eq_piUniv]
      exact Fintype_sum_fn_prod (R := ℂ) (ι := Site) (α := ZMod p)
        (fun (site : Site) (a : ZMod p) => phase p (f site * a))
    _ = if f = 0 then (p : ℂ) ^ Fintype.card Site else 0 := by
      simp_rw [sum_phase_smul]
      by_cases hf : f = 0
      · subst f
        simp
      · have ⟨s, hs⟩ : ∃ site : Site, f site ≠ 0 := by
          by_contra h
          apply hf
          ext site
          by_contra hs'
          exact h ⟨site, hs'⟩
        rw [Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs]), if_neg hf]
end QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS

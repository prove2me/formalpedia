-- Prove2me | solution 1 for QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.sum_characterKet_rankOne_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:55:33.33332+00:00
-- url     : https://prove2.me/submissions/75cbe362-efd0-40db-8e35-2ca2573dcbee

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
theorem _root_.solution :
    (∑ e : PrimeQuditRegisterLabel p Site,
        (InnerProductSpace.rankOne ℂ (characterKet p e) (characterKet p e)).toLinearMap) = 1 := by
  apply LinearMap.ext
  intro psi
  ext x
  simp only [LinearMap.sum_apply, InnerProductSpace.toLinearMap_rankOne,
    LinearMap.smulRight_apply, innerₛₗ_apply_apply, PiLp.inner_apply, RCLike.inner_apply']
  rw [← PiLp.projₗ_apply (p := 2) (𝕜 := ℂ)
    (β := fun _ : PrimeQuditRegisterLabel p Site => ℂ) x]
  rw [map_sum]
  simp only [PiLp.projₗ_apply, PiLp.smul_apply, Module.End.one_apply]
  change (∑ e : PrimeQuditRegisterLabel p Site, (∑ y : PrimeQuditRegisterLabel p Site,
      starRingEnd ℂ (characterKet p e y) * psi y) * characterKet p e x) = psi x
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hsummand (y : PrimeQuditRegisterLabel p Site) (e : PrimeQuditRegisterLabel p Site) :
      starRingEnd ℂ (phase p (registerPairing p e y)) * phase p (registerPairing p e x) =
        phase p (registerPairing p (x - y) e) := by
    rw [phase_conj, ← phase_add]
    congr 1
    simp only [registerPairing]
    rw [Finset.sum_congr rfl (fun site _ => mul_comm (e site) (y site))]
    rw [Finset.sum_congr rfl (fun site _ => mul_comm (e site) (x site))]
    conv_rhs =>
      rw [Finset.sum_congr rfl (fun site _ => by
        show (x - y) site * e site = x site * e site - y site * e site
        rw [Pi.sub_apply]
        exact sub_mul (x site) (y site) (e site))]
    rw [Finset.sum_sub_distrib]
    abel
  have hmain (y : PrimeQuditRegisterLabel p Site) :
      (∑ e : PrimeQuditRegisterLabel p Site, (starRingEnd ℂ (characterKet p e y) * psi y) *
          characterKet p e x) =
        psi y * (((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) *
          ((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) *
            if y = x then (p : ℂ) ^ Fintype.card Site else 0) := by
    rw [Finset.sum_congr rfl (fun e _ => calc
      (starRingEnd ℂ (characterKet p e y) * psi y) * characterKet p e x =
          ((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) *
            (((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) *
              (psi y * (starRingEnd ℂ (phase p (registerPairing p e y)) *
                phase p (registerPairing p e x)))) := by
        simp only [characterKet_apply, map_mul, map_pow, map_inv₀, Complex.conj_ofReal]
        ring
      _ = ((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) *
            (((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) *
              (psi y * phase p (registerPairing p (x - y) e))) := by
        rw [hsummand y e])]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [sum_register_phase p (x - y)]
    by_cases hyx : y = x
    · subst y
      simp
      ring
    · have hne : x - y ≠ 0 := by
        intro h
        exact hyx (sub_eq_zero.mp h).symm
      simp [hyx, hne]
  rw [Finset.sum_congr rfl (fun y _ => hmain y)]
  rw [Finset.sum_eq_single x]
  · rw [show (if x = x then (p : ℂ) ^ Fintype.card Site else 0) =
          (p : ℂ) ^ Fintype.card Site by simp]
    rw [show (Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site *
        (Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site *
          (p : ℂ) ^ Fintype.card Site = 1 by
      exact registerNorm_sq_mul_pow p]
    simp
  · intro y _ hyx
    simp [hyx]
  · intro hx
    exact (hx (Finset.mem_univ x)).elim
end QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS

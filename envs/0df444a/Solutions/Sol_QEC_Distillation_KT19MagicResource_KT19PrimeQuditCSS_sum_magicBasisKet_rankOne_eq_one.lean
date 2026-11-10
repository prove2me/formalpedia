-- Prove2me | solution 1 for QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.sum_magicBasisKet_rankOne_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:53:26.26702+00:00
-- url     : https://prove2.me/submissions/5154d002-b871-44d7-9340-6b9cb3157f9d

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
theorem _root_.solution :
    (∑ a : ZMod p,
        (InnerProductSpace.rankOne ℂ (magicBasisKet p a)
          (magicBasisKet p a)).toLinearMap) = 1 := by
  apply LinearMap.ext
  intro psi
  ext x
  simp only [LinearMap.sum_apply, InnerProductSpace.toLinearMap_rankOne,
    LinearMap.smulRight_apply, innerₛₗ_apply_apply, PiLp.inner_apply, RCLike.inner_apply']
  rw [← PiLp.projₗ_apply (p := 2) (𝕜 := ℂ) (β := fun _ : ZMod p => ℂ) x]
  rw [map_sum]
  simp only [PiLp.projₗ_apply, PiLp.smul_apply, Module.End.one_apply]
  change (∑ a : ZMod p, (∑ y : ZMod p,
      starRingEnd ℂ (magicBasisKet p a y) * psi y) * magicBasisKet p a x) = psi x
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [magicBasisKet_apply]
  simp_rw [magicBasisAmplitude]
  have hsummand (y : ZMod p) (a : ZMod p) :
      starRingEnd ℂ (phase p (a * y + y ^ 3)) * phase p (a * x + x ^ 3) =
        phase p ((x - y) * a + (x ^ 3 - y ^ 3)) := by
    rw [phase_conj, ← phase_add]
    congr 1
    ring
  have hmain (y : ZMod p) :
      (∑ a : ZMod p, (starRingEnd ℂ ((Real.sqrt (p : Real) : Complex)⁻¹ *
            phase p (a * y + y ^ 3)) * psi y) *
          ((Real.sqrt (p : Real) : Complex)⁻¹ * phase p (a * x + x ^ 3))) =
        psi y * ((Real.sqrt (p : Real) : Complex)⁻¹ *
          (Real.sqrt (p : Real) : Complex)⁻¹ *
            if y = x then (p : ℂ) else 0) := by
    rw [Finset.sum_congr rfl (fun a _ => calc
      (starRingEnd ℂ ((Real.sqrt (p : Real) : Complex)⁻¹ * phase p (a * y + y ^ 3)) * psi y) *
          ((Real.sqrt (p : Real) : Complex)⁻¹ * phase p (a * x + x ^ 3)) =
          (Real.sqrt (p : Real) : Complex)⁻¹ * ((Real.sqrt (p : Real) : Complex)⁻¹ *
            (psi y * (starRingEnd ℂ (phase p (a * y + y ^ 3)) *
              phase p (a * x + x ^ 3)))) := by
        rw [map_mul, map_inv₀, Complex.conj_ofReal]
        ring
      _ = (Real.sqrt (p : Real) : Complex)⁻¹ * ((Real.sqrt (p : Real) : Complex)⁻¹ *
            (psi y * phase p ((x - y) * a + (x ^ 3 - y ^ 3)))) := by
        rw [hsummand y a])]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun a _ => by rw [phase_add, mul_comm])]
    rw [← Finset.mul_sum]
    rw [sum_phase_smul]
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
  · rw [show (if x = x then (p : ℂ) else 0) = (p : ℂ) by simp]
    rw [show (Real.sqrt (p : Real) : Complex)⁻¹ *
        (Real.sqrt (p : Real) : Complex)⁻¹ * (p : ℂ) = 1 by
      exact singleNorm_sq_mul_p p]
    simp
  · intro y _ hyx
    simp [hyx]
  · intro hx
    exact (hx (Finset.mem_univ x)).elim
end QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS

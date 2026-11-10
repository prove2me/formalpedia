-- Prove2me | solution 1 for QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.magicBasisKet_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:53:28.639445+00:00
-- url     : https://prove2.me/submissions/4b68c19d-db07-4ebd-bde6-4a5c52d06890

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
theorem _root_.solution (a b : ZMod p) :
    inner ℂ (magicBasisKet p a) (magicBasisKet p b) = if a = b then 1 else 0 := by
  rw [PiLp.inner_apply]
  simp_rw [magicBasisKet_apply]
  rw [Finset.sum_congr rfl (fun x _ => by
    have hphase :
        starRingEnd ℂ (phase p (a * x + x ^ 3)) * phase p (b * x + x ^ 3) =
          phase p ((b - a) * x) := by
      rw [phase_conj, ← phase_add]
      congr 1
      ring
    calc
      inner ℂ ((Real.sqrt (p : Real) : Complex)⁻¹ * phase p (a * x + x ^ 3))
          ((Real.sqrt (p : Real) : Complex)⁻¹ * phase p (b * x + x ^ 3)) =
          (Real.sqrt (p : Real) : Complex)⁻¹ * (Real.sqrt (p : Real) : Complex)⁻¹ *
            (starRingEnd ℂ (phase p (a * x + x ^ 3)) * phase p (b * x + x ^ 3)) := by
        rw [RCLike.inner_apply', map_mul, map_inv₀, Complex.conj_ofReal]
        ring
      _ = (Real.sqrt (p : Real) : Complex)⁻¹ * (Real.sqrt (p : Real) : Complex)⁻¹ *
            phase p ((b - a) * x) := by
        rw [hphase])]
  rw [← Finset.mul_sum]
  rw [sum_phase_smul]
  by_cases hab : a = b
  · subst b
    simp [singleNorm_sq_mul_p]
  · have hne : b - a ≠ 0 := by
      intro h
      exact hab (sub_eq_zero.mp h).symm
    simp [hab, hne]
end QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS

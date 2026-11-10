-- Prove2me | solution 1 for QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.phase_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:49:30.926773+00:00
-- url     : https://prove2.me/submissions/66188886-43b7-4d2f-8583-cbd0a3cd07e4

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
theorem _root_.solution (x : ZMod p) :
    phase p x = 1 ↔ x = 0 := by
  constructor
  · intro hx
    by_contra hx0
    have hshift : (ZMod.stdAddChar (N := p)).mulShift x = 1 := by
      ext y
      change phase p (x * y) = 1
      calc
        phase p (x * y) = phase p (y * x) := by rw [mul_comm]
        _ = phase p (y.val • x) := by
          congr 1
          rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
        _ = (phase p x) ^ y.val := AddChar.map_nsmul_eq_pow _ _ _
        _ = 1 := by simp [hx]
    exact (ZMod.isPrimitive_stdAddChar p hx0 hshift).elim
  · intro hx
    subst hx
    exact phase_zero p
end QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS

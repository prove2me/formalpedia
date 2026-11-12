-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.tMagicState_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:53:24.293487+00:00
-- url     : https://prove2.me/submissions/122dd4fa-215e-4dbb-8ef2-cdff5a82b770

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_blochProjector_injective
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


section
noncomputable section
namespace QEC
namespace Distillation
namespace OneQubitMagic
open Semantics Semantics.Qubit
private theorem signedCoordinateValue_injective :
    Function.Injective signedCoordinateValue := by
  intro a b hab
  cases a <;> cases b <;> simp_all [signedCoordinateValue]
private theorem tBlochOfDirection_injective :
    Function.Injective tBlochOfDirection := by
  intro d e hde
  apply Subtype.ext
  funext i
  apply signedCoordinateValue_injective
  have hi := congrFun hde i
  simp only [tBlochOfDirection] at hi
  have hinv : (Real.sqrt 3)⁻¹ ≠ 0 :=
    inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))
  have hvalue :
      (signedCoordinateValue (d.1 i) : Real) = signedCoordinateValue (e.1 i) :=
    mul_right_cancel₀ hinv hi
  exact_mod_cast hvalue
end OneQubitMagic
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution : Function.Injective tMagicStateOfDirection := by
  intro d e hde
  apply tBlochOfDirection_injective
  apply blochProjector_injective
  simpa [tMagicStateOfDirection, blochDensity] using congrArg
    (fun rho : DensityOperator QubitSpace => rho.toOperator) hde
end QEC.Distillation.OneQubitMagic

-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.hMagicState_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:53:39.878663+00:00
-- url     : https://prove2.me/submissions/4d05a9e0-ed9d-457b-a2f6-2b1b02d4e599

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
private theorem hBlochOfDirection_injective :
    Function.Injective hBlochOfDirection := by
  intro d e hde
  apply Subtype.ext
  funext i
  apply signedCoordinateValue_injective
  have hi := congrFun hde i
  simp only [hBlochOfDirection] at hi
  have hinv : (Real.sqrt 2)⁻¹ ≠ 0 :=
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
theorem _root_.solution : Function.Injective hMagicStateOfDirection := by
  intro d e hde
  apply hBlochOfDirection_injective
  apply blochProjector_injective
  simpa [hMagicStateOfDirection, blochDensity] using congrArg
    (fun rho : DensityOperator QubitSpace => rho.toOperator) hde
end QEC.Distillation.OneQubitMagic

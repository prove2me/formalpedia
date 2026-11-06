-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.supportedOn_projector_comp_toOperator_comp_projector_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:58:49.406218+00:00
-- url     : https://prove2.me/submissions/d1d66364-c98c-4160-a283-cc005bc1a7c7

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_projector_comp_eq_self
import Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_comp_projector_eq_self
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped ComplexOrder
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
namespace QEC.Semantics.DensityOperator
theorem _root_.solution
    (C : QuantumCode H) (rho : DensityOperator H) (hρ : SupportedOn C rho) :
    C.projector.comp (rho.toOperator.comp C.projector) = rho.toOperator := by
  ext v
  have hleft := congrArg (fun A : Operator H => A (C.projector v))
    (supportedOn_projector_comp_eq_self C rho hρ)
  have hright := congrArg (fun A : Operator H => A v)
    (supportedOn_comp_projector_eq_self C rho hρ)
  exact hleft.trans hright
end QEC.Semantics.DensityOperator

-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.supportedOn_iff_projector_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:17:59.392425+00:00
-- url     : https://prove2.me/submissions/d6c904c7-0c91-4d3e-abf0-c9b1021992cb

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_eq_self_iff_mem
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_eq_self_of_mem
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
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
theorem _root_.solution (C : QuantumCode H) (rho : DensityOperator H) :
    SupportedOn C rho ↔ C.projector.comp rho.toOperator = rho.toOperator := by
  constructor
  · intro hρ
    ext v
    exact C.projector_eq_self_of_mem (hρ v)
  · intro hρ v
    have hv := congrArg (fun A : Operator H => A v) hρ
    change C.projector (rho.toOperator v) = rho.toOperator v at hv
    exact (C.projector_eq_self_iff_mem).1 hv
end QEC.Semantics.DensityOperator

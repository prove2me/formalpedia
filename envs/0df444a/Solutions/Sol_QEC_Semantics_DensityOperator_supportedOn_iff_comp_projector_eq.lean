-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.supportedOn_iff_comp_projector_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:45:39.852939+00:00
-- url     : https://prove2.me/submissions/fa051e3e-eb87-45ce-9558-72c2d102b1f0

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_adjoint_eq_self
import Theorems.Thm_QEC_Semantics_DensityOperator_toOperator_adjoint_eq_self
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_iff_projector_comp_eq
import Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_projector_comp_eq_self
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
    SupportedOn C rho ↔ rho.toOperator.comp C.projector = rho.toOperator := by
  constructor
  · intro hρ
    have hleft : C.projector.comp rho.toOperator = rho.toOperator :=
      supportedOn_projector_comp_eq_self C rho hρ
    have hadj := congrArg LinearMap.adjoint hleft
    simpa [LinearMap.adjoint_comp, QuantumCode.projector_adjoint_eq_self,
      toOperator_adjoint_eq_self] using hadj
  · intro hright
    refine (supportedOn_iff_projector_comp_eq C rho).2 ?_
    have hadj := congrArg LinearMap.adjoint hright
    simpa [LinearMap.adjoint_comp, QuantumCode.projector_adjoint_eq_self,
      toOperator_adjoint_eq_self] using hadj
end QEC.Semantics.DensityOperator

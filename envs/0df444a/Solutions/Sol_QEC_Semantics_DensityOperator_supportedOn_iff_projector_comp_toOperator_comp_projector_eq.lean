-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.supportedOn_iff_projector_comp_toOperator_comp_projector_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:43:22.348194+00:00
-- url     : https://prove2.me/submissions/470e26c4-729d-4cfd-9637-a8d32a13e271

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_mem_carrier
import Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_projector_comp_toOperator_comp_projector_eq_self

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
    (C : QuantumCode H) (rho : DensityOperator H) :
    SupportedOn C rho ↔ C.projector.comp (rho.toOperator.comp C.projector) = rho.toOperator := by
  constructor
  · exact supportedOn_projector_comp_toOperator_comp_projector_eq_self C rho
  · intro hρ v
    have hv := congrArg (fun A : Operator H => A v) hρ
    change C.projector (rho.toOperator (C.projector v)) = rho.toOperator v at hv
    have hmem : C.projector (rho.toOperator (C.projector v)) ∈ C.carrier :=
      C.projector_mem_carrier (rho.toOperator (C.projector v))
    exact hv ▸ hmem
end QEC.Semantics.DensityOperator

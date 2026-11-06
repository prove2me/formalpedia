-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.supportedOn_comp_projector_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:51:03.716883+00:00
-- url     : https://prove2.me/submissions/61f750d5-02fc-4089-9a98-8f1056f6be89

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_iff_comp_projector_eq

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
theorem _root_.solution (C : QuantumCode H) (rho : DensityOperator H)
    (hρ : SupportedOn C rho) :
    rho.toOperator.comp C.projector = rho.toOperator :=
  (supportedOn_iff_comp_projector_eq C rho).1 hρ
end QEC.Semantics.DensityOperator

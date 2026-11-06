-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.supportedOn_projector_comp_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:23:15.070611+00:00
-- url     : https://prove2.me/submissions/2f53fbf8-43ea-416f-a318-12797d231faa

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_iff_projector_comp_eq

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
    C.projector.comp rho.toOperator = rho.toOperator :=
  (supportedOn_iff_projector_comp_eq C rho).1 hρ
end QEC.Semantics.DensityOperator

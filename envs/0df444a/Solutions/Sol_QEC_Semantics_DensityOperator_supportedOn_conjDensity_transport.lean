-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.supportedOn_conjDensity_transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:37:55.778229+00:00
-- url     : https://prove2.me/submissions/17ecd233-6b57-4f7f-be77-983c926328dc

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions
import Theorems.Thm_QEC_Semantics_QuantumCode_transportedBy_transport
import Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_conjDensity_of_transportedBy

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder
open QEC.Semantics.DensityOperator
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
namespace QEC.Semantics.DensityOperator
theorem _root_.solution
    (U : UnitaryTransport H K) (C : QuantumCode H) (rho : DensityOperator H)
    (hρ : SupportedOn C rho) :
    SupportedOn (C.transport U) (U.conjDensity rho) :=
  supportedOn_conjDensity_of_transportedBy U (QuantumCode.transportedBy_transport U C) hρ
end QEC.Semantics.DensityOperator

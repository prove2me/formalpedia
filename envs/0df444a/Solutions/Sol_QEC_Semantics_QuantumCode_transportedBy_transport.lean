-- Prove2me | solution 1 for QEC.Semantics.QuantumCode.transportedBy_transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:34:22.95905+00:00
-- url     : https://prove2.me/submissions/efc98744-c37e-4dd6-ba99-c03f4c4235ed

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_QuantumCode_mem_transport_carrier_iff
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder
open QEC.Semantics.QuantumCode
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
namespace QEC.Semantics.QuantumCode
theorem _root_.solution (U : UnitaryTransport H K) (C : QuantumCode H) :
    TransportedBy U C (C.transport U) := by
  intro x
  simpa using (mem_transport_carrier_iff U C (x := x)).symm
end QEC.Semantics.QuantumCode

-- Prove2me | solution 2 for QEC.Semantics.DensityOperator.supportedOn_conjDensity_transport_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:42:57.632846+00:00
-- url     : https://prove2.me/submissions/3b4d6c6a-3810-4f1a-9a67-c5eec3c76d7f

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_QuantumCode_mem_transport_carrier_iff
import Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_conjDensity_transport
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply

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
    (U : UnitaryTransport H K) (C : QuantumCode H) (rho : DensityOperator H) :
    SupportedOn (C.transport U) (U.conjDensity rho) ↔ SupportedOn C rho := by
  constructor
  · intro hρ x
    have hx := hρ (U.toLinearEquiv x)
    rw [UnitaryTransport.conjDensity_apply] at hx
    simpa using (QuantumCode.mem_transport_carrier_iff U C).1 hx
  · exact supportedOn_conjDensity_transport U C rho
end QEC.Semantics.DensityOperator

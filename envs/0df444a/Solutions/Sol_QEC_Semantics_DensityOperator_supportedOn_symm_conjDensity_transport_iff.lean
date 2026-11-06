-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.supportedOn_symm_conjDensity_transport_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:17:16.760963+00:00
-- url     : https://prove2.me/submissions/359b7f06-c4c4-4a90-89b4-a847e4cfc2b3

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_QuantumCode_mem_transport_carrier_iff_symm
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
    (U : UnitaryTransport H K) (C : QuantumCode H) (rho : DensityOperator K) :
    SupportedOn C (U.symm.conjDensity rho) ↔ SupportedOn (C.transport U) rho := by
  constructor
  · intro hρ y
    have hy := hρ (U.toLinearEquiv.symm y)
    rw [UnitaryTransport.conjDensity_apply] at hy
    exact (QuantumCode.mem_transport_carrier_iff_symm U C).2 (by
      simpa [UnitaryTransport.symm] using hy)
  · intro hρ x
    have hx := hρ (U.toLinearEquiv x)
    rw [UnitaryTransport.conjDensity_apply]
    exact (QuantumCode.mem_transport_carrier_iff_symm U C).1 (by
      simpa using hx)
end QEC.Semantics.DensityOperator

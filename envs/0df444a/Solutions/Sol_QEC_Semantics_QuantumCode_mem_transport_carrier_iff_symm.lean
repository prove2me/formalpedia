-- Prove2me | solution 1 for QEC.Semantics.QuantumCode.mem_transport_carrier_iff_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:02:03.267581+00:00
-- url     : https://prove2.me/submissions/6b81cd8b-9121-4b31-a8be-86a28c443083

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
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
theorem _root_.solution (U : UnitaryTransport H K) (C : QuantumCode H)
    {y : K} :
    y ∈ (C.transport U).carrier ↔ U.toLinearEquiv.symm y ∈ C.carrier := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hy
    refine ⟨U.toLinearEquiv.symm y, hy, ?_⟩
    simp
end QEC.Semantics.QuantumCode

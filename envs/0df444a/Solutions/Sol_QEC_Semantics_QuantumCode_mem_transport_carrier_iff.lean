-- Prove2me | solution 1 for QEC.Semantics.QuantumCode.mem_transport_carrier_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:16:57.227934+00:00
-- url     : https://prove2.me/submissions/967e8c4f-97c2-47a9-8df3-35f5232b763d

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
open QEC.Semantics.QuantumCode
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
namespace QEC.Semantics.QuantumCode
theorem _root_.solution (U : UnitaryTransport H K) (C : QuantumCode H)
    {x : H} :
    U.toLinearEquiv x ∈ (C.transport U).carrier ↔ x ∈ C.carrier := by
  rw [mem_transport_carrier_iff_symm]
  simp
end QEC.Semantics.QuantumCode

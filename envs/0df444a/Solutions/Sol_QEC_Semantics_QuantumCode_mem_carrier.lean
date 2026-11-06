-- Prove2me | solution 1 for QEC.Semantics.QuantumCode.mem_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:33:50.680277+00:00
-- url     : https://prove2.me/submissions/df41ed36-1475-4f73-97a0-023c23949cda

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder
open QEC.Semantics.QuantumCode
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
namespace QEC.Semantics.QuantumCode
theorem _root_.solution (C : QuantumCode H) {v : H} :
    v ∈ C.carrier ↔ v ∈ (C : Submodule Complex H) :=
  Iff.rfl
end QEC.Semantics.QuantumCode

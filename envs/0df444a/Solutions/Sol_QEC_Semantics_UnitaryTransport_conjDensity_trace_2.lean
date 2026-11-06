-- Prove2me | solution 2 for QEC.Semantics.UnitaryTransport.conjDensity_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:42:54.436789+00:00
-- url     : https://prove2.me/submissions/8c18fab5-f637-4203-8393-426ff0460d9a

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder
open QEC.Semantics.UnitaryTransport
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
namespace QEC.Semantics.UnitaryTransport
theorem _root_.solution (U : UnitaryTransport H K)
    (rho : DensityOperator H) :
    LinearMap.trace Complex K (U.conjDensity rho).toOperator = 1 :=
  (U.conjDensity rho).trace_one
end QEC.Semantics.UnitaryTransport

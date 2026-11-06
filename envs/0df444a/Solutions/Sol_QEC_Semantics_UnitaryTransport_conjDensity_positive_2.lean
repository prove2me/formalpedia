-- Prove2me | solution 2 for QEC.Semantics.UnitaryTransport.conjDensity_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:42:56.616223+00:00
-- url     : https://prove2.me/submissions/f0036e8e-4c31-4fa2-b4e8-976babe1e15d

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
    LinearMap.IsPositive (U.conjDensity rho).toOperator :=
  (U.conjDensity rho).positive
end QEC.Semantics.UnitaryTransport

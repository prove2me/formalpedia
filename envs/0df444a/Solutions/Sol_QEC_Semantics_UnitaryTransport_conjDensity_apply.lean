-- Prove2me | solution 1 for QEC.Semantics.UnitaryTransport.conjDensity_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:56:33.793805+00:00
-- url     : https://prove2.me/submissions/7a13431f-e726-47a6-8ac9-dbc68a4ff00d

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
    (rho : DensityOperator H) (x : K) :
    (U.conjDensity rho).toOperator x =
      U.toLinearEquiv (rho.toOperator (U.toLinearEquiv.symm x)) :=
  rfl
end QEC.Semantics.UnitaryTransport

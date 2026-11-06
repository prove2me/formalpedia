-- Prove2me | solution 1 for QEC.Semantics.UnitaryTransport.conjDensity_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:56:22.564839+00:00
-- url     : https://prove2.me/submissions/375e31d6-1d25-424b-b693-4ce9a6f27d2f

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
    (U.conjDensity rho).toOperator = U.conjOperator rho.toOperator :=
  rfl
end QEC.Semantics.UnitaryTransport

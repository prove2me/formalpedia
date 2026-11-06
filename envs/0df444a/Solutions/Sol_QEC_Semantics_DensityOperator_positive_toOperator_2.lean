-- Prove2me | solution 2 for QEC.Semantics.DensityOperator.positive_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:42:17.563964+00:00
-- url     : https://prove2.me/submissions/aa00a53c-7208-448f-825e-e18208f7c698

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder
open QEC.Semantics.DensityOperator
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
namespace QEC.Semantics.DensityOperator
theorem _root_.solution (rho : DensityOperator H) :
    LinearMap.IsPositive rho.toOperator :=
  rho.positive
end QEC.Semantics.DensityOperator

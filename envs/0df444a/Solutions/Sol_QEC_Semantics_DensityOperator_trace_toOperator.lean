-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.trace_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:32:25.166196+00:00
-- url     : https://prove2.me/submissions/242d681b-ee60-47cd-924f-e8b4f49e9ef6

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
    LinearMap.trace Complex H rho.toOperator = 1 :=
  rho.trace_one
end QEC.Semantics.DensityOperator

-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.projectionTrace_add_complementTrace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:50:07.352069+00:00
-- url     : https://prove2.me/submissions/1ed04efe-71ee-4c37-ba88-5c7c24303e77

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Theorems.Thm_QEC_Semantics_trace_projection_add_complement

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
open QEC.Semantics.DensityOperator
namespace QEC.Semantics.DensityOperator
theorem _root_.solution (P : Operator H) (rho : DensityOperator H) :
    LinearMap.trace Complex H (P * rho.toOperator) +
      LinearMap.trace Complex H ((1 - P) * rho.toOperator) = 1 := by
  rw [trace_projection_add_complement, rho.trace_one]
end QEC.Semantics.DensityOperator

-- Prove2me | solution 1 for QEC.Semantics.projectedTail_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:37:49.139628+00:00
-- url     : https://prove2.me/submissions/8fb5989f-b677-4787-8eb4-6962a1c28072

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics
theorem _root_.solution (P A : Operator H) (hP : IsStarProjection P) :
    LinearMap.trace Complex H (projectedTail P A) =
      LinearMap.trace Complex H ((1 - P) * A) := by
  have hQ : IsStarProjection (1 - P) := hP.one_sub
  rw [projectedTail, LinearMap.trace_mul_cycle]
  rw [hQ.isIdempotentElem.eq]
end QEC.Semantics

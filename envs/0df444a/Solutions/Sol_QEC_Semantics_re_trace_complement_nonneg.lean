-- Prove2me | solution 1 for QEC.Semantics.re_trace_complement_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:58:24.497969+00:00
-- url     : https://prove2.me/submissions/45844d30-d41b-4d5f-9379-51fbbadeceb9

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Theorems.Thm_QEC_Semantics_traceNorm_nonneg
import Theorems.Thm_QEC_Semantics_traceNorm_projectedTail_eq_re_trace

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics
theorem _root_.solution [Nontrivial H]
    (P A : Operator H) (hP : IsStarProjection P) (hA : LinearMap.IsPositive A) :
    0 ≤ Complex.re (LinearMap.trace Complex H ((1 - P) * A)) := by
  rw [← traceNorm_projectedTail_eq_re_trace P A hP hA]
  exact traceNorm_nonneg _
end QEC.Semantics

-- Prove2me | solution 1 for QEC.Semantics.traceNorm_projectedTail_eq_re_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:49:49.979712+00:00
-- url     : https://prove2.me/submissions/e561933f-ef67-477d-bda8-63f97bb38c89

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Theorems.Thm_QEC_Semantics_traceNorm_eq_re_trace_of_positive
import Theorems.Thm_QEC_Semantics_projectedTail_positive
import Theorems.Thm_QEC_Semantics_projectedTail_trace

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
    traceNorm (projectedTail P A) =
      Complex.re (LinearMap.trace Complex H ((1 - P) * A)) := by
  rw [traceNorm_eq_re_trace_of_positive (projectedTail P A)
    (projectedTail_positive P A hP hA)]
  rw [projectedTail_trace P A hP]
end QEC.Semantics

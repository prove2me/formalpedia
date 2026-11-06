-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.traceNorm_projectedTail_eq_complementTrace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:58:30.956324+00:00
-- url     : https://prove2.me/submissions/83b2fce3-5fb3-4b05-a70a-ca66c202a64b

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Theorems.Thm_QEC_Semantics_traceNorm_projectedTail_eq_re_trace

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
theorem _root_.solution [Nontrivial H]
    (P : Operator H) (hP : IsStarProjection P) (rho : DensityOperator H) :
    traceNorm (projectedTail P rho.toOperator) =
      Complex.re (LinearMap.trace Complex H ((1 - P) * rho.toOperator)) :=
  traceNorm_projectedTail_eq_re_trace P rho.toOperator hP rho.positive
end QEC.Semantics.DensityOperator

-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.traceNorm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:50:39.706577+00:00
-- url     : https://prove2.me/submissions/96f26f93-853e-4759-b427-d7905d6c6578

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Theorems.Thm_QEC_Semantics_traceNorm_eq_re_trace_of_positive

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
theorem _root_.solution [Nontrivial H] (rho : DensityOperator H) :
    traceNorm rho.toOperator = 1 := by
  rw [traceNorm_eq_re_trace_of_positive rho.toOperator rho.positive, rho.trace_one]
  norm_num
end QEC.Semantics.DensityOperator

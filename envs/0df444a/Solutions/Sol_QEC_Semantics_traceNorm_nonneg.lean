-- Prove2me | solution 1 for QEC.Semantics.traceNorm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:09:36.780375+00:00
-- url     : https://prove2.me/submissions/f1f7fb70-434a-41de-a93f-3f3b84d93751

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
theorem _root_.solution (A : Operator H) : 0 ≤ traceNorm A :=
  ContinuousLinearMap.opNorm_nonneg _
end QEC.Semantics

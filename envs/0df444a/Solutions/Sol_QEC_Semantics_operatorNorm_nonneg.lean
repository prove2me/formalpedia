-- Prove2me | solution 1 for QEC.Semantics.operatorNorm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:13:26.382565+00:00
-- url     : https://prove2.me/submissions/6c135f62-b6a3-4d86-be70-0ed86587cc7f

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
theorem _root_.solution (A : Operator H) : 0 ≤ operatorNorm A :=
  ContinuousLinearMap.opNorm_nonneg _
end QEC.Semantics

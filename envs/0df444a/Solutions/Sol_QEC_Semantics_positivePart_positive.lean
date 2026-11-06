-- Prove2me | solution 1 for QEC.Semantics.positivePart_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:12:02.14231+00:00
-- url     : https://prove2.me/submissions/735eb6a6-733e-417a-9725-87a325bfda5a

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
theorem _root_.solution (A : Operator H) : LinearMap.IsPositive (positivePart A) := by
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).mp (CFC.posPart_nonneg _)
end QEC.Semantics

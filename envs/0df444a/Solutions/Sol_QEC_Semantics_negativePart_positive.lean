-- Prove2me | solution 1 for QEC.Semantics.negativePart_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:12:03.604019+00:00
-- url     : https://prove2.me/submissions/00edb27f-86ba-43f2-b8a4-bd1c131299a5

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
theorem _root_.solution (A : Operator H) : LinearMap.IsPositive (negativePart A) := by
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).mp (CFC.negPart_nonneg _)
end QEC.Semantics

-- Prove2me | solution 1 for QEC.Semantics.positiveSupportProjection_mul_negativeSupportProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:49:58.620926+00:00
-- url     : https://prove2.me/submissions/e2f6da6a-387e-4935-8dab-06deecece310

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Theorems.Thm_QEC_Semantics_parts_range_isOrtho

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics
theorem _root_.solution (A : Operator H) :
    positiveSupportProjection A * negativeSupportProjection A = 0 := by
  exact (parts_range_isOrtho A).starProjection_comp_starProjection
end QEC.Semantics

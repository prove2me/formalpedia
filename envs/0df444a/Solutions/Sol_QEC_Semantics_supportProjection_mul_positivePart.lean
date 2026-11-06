-- Prove2me | solution 1 for QEC.Semantics.supportProjection_mul_positivePart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:37:20.148907+00:00
-- url     : https://prove2.me/submissions/cb0aeeea-8a0a-4092-b86c-301d4018ca31

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
theorem _root_.solution (A : Operator H) :
    positiveSupportProjection A * (LinearMap.toContinuousLinearMap A)⁺ =
      (LinearMap.toContinuousLinearMap A)⁺ := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr ⟨x, rfl⟩
end QEC.Semantics

-- Prove2me | solution 1 for QEC.Semantics.supportProjection_mul_negativePart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:37:22.247476+00:00
-- url     : https://prove2.me/submissions/57cd8d90-1483-4656-9af2-e9dbe65ee08b

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
    negativeSupportProjection A * (LinearMap.toContinuousLinearMap A)⁻ =
      (LinearMap.toContinuousLinearMap A)⁻ := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr ⟨x, rfl⟩
end QEC.Semantics

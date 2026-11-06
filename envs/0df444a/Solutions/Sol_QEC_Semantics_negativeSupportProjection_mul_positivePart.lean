-- Prove2me | solution 1 for QEC.Semantics.negativeSupportProjection_mul_positivePart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:37:35.279617+00:00
-- url     : https://prove2.me/submissions/cffa09eb-5a2c-4a16-9201-10a1d8224a6a

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
    negativeSupportProjection A * (LinearMap.toContinuousLinearMap A)⁺ = 0 := by
  ext x
  unfold negativeSupportProjection
  change ((LinearMap.toContinuousLinearMap A)⁻).range.starProjection
    ((LinearMap.toContinuousLinearMap A)⁺ x) = 0
  rw [Submodule.starProjection_apply_eq_zero_iff]
  exact (Submodule.isOrtho_iff_le.mp (parts_range_isOrtho A)) ⟨x, rfl⟩
end QEC.Semantics

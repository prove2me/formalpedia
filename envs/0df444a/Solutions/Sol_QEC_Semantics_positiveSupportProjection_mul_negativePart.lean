-- Prove2me | solution 1 for QEC.Semantics.positiveSupportProjection_mul_negativePart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:37:28.783679+00:00
-- url     : https://prove2.me/submissions/d3283b11-423d-4a3c-88f8-d921f10d941a

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
    positiveSupportProjection A * (LinearMap.toContinuousLinearMap A)⁻ = 0 := by
  ext x
  unfold positiveSupportProjection
  change ((LinearMap.toContinuousLinearMap A)⁺).range.starProjection
    ((LinearMap.toContinuousLinearMap A)⁻ x) = 0
  rw [Submodule.starProjection_apply_eq_zero_iff]
  exact (Submodule.isOrtho_iff_le.mp (parts_range_isOrtho A).symm) ⟨x, rfl⟩
end QEC.Semantics

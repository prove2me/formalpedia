-- Prove2me | solution 1 for QEC.Semantics.parts_range_isOrtho
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:12:04.242762+00:00
-- url     : https://prove2.me/submissions/f804bf9c-5df3-4f6a-95d7-9bc83076b1ac

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



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
    ((LinearMap.toContinuousLinearMap A)⁺).range ⟂
      ((LinearMap.toContinuousLinearMap A)⁻).range := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro u hu v hv
  rcases hu with ⟨x, rfl⟩
  rcases hv with ⟨y, rfl⟩
  have hpos : ((LinearMap.toContinuousLinearMap A)⁺).IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mp (CFC.posPart_nonneg _)
  calc
    inner Complex ((LinearMap.toContinuousLinearMap A)⁺ x)
        ((LinearMap.toContinuousLinearMap A)⁻ y) =
      inner Complex x
        ((LinearMap.toContinuousLinearMap A)⁺
          ((LinearMap.toContinuousLinearMap A)⁻ y)) :=
        hpos.inner_left_eq_inner_right x _
    _ = 0 := by
      simp only [← ContinuousLinearMap.mul_apply, CFC.posPart_mul_negPart,
        ContinuousLinearMap.zero_apply, inner_zero_right]
end QEC.Semantics

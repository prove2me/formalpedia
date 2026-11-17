-- Prove2me | solution 1 for Scratch.TateZ2xZ10Reduction.translateToOriginTangent_a4_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:02:29.557433+00:00
-- url     : https://prove2.me/submissions/0e4422aa-a142-4dbf-9155-dbc323924244

import Mathlib
import Definitions.Def_TateZ2xZ10
import Definitions.Def_TateZ2xZ10Reduction

/-! Proofs of the lemmas stated in `Theorems.Thm_TateNormalForm_Z2xZ10Reduction` and their helpers. -/

open scoped WeierstrassCurve.Affine

namespace Scratch.TateZ2xZ10Reduction

noncomputable section

@[simp] lemma tateNormalFormCurve_a₁ (b c : ℚ) :
    (tateNormalFormCurve b c).a₁ = 1 - c := rfl

@[simp] lemma tateNormalFormCurve_a₂ (b c : ℚ) :
    (tateNormalFormCurve b c).a₂ = -b := rfl

@[simp] lemma tateNormalFormCurve_a₃ (b c : ℚ) :
    (tateNormalFormCurve b c).a₃ = -b := rfl

@[simp] lemma tateNormalFormCurve_a₄ (b c : ℚ) :
    (tateNormalFormCurve b c).a₄ = 0 := rfl

@[simp] lemma tateNormalFormCurve_a₆ (b c : ℚ) :
    (tateNormalFormCurve b c).a₆ = 0 := rfl

@[simp] lemma translateToOriginTangent_a₁ (W : WeierstrassCurve ℚ) (x₀ y₀ : ℚ) :
    ((translateToOriginTangent W x₀ y₀) • W).a₁ =
      W.a₁ + 2 * tangentSlope W x₀ y₀ := by
  rw [WeierstrassCurve.variableChange_a₁]
  simp [translateToOriginTangent]

@[simp] lemma translateToOriginTangent_a₂ (W : WeierstrassCurve ℚ) (x₀ y₀ : ℚ) :
    ((translateToOriginTangent W x₀ y₀) • W).a₂ =
      W.a₂ - tangentSlope W x₀ y₀ * W.a₁ + 3 * x₀ - tangentSlope W x₀ y₀ ^ 2 := by
  rw [WeierstrassCurve.variableChange_a₂]
  simp [translateToOriginTangent]

/-- If the point is not 2-torsion, the tangent choice kills the linear `X` term. -/
theorem _root_.solution
    (W : WeierstrassCurve ℚ) {x₀ y₀ : ℚ}
    (hden : 2 * y₀ + W.a₁ * x₀ + W.a₃ ≠ 0) :
    ((translateToOriginTangent W x₀ y₀) • W).a₄ = 0 := by
  have hs :
      tangentSlope W x₀ y₀ * (2 * y₀ + W.a₁ * x₀ + W.a₃) =
        3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀ := by
    unfold tangentSlope
    exact div_mul_cancel₀ _ hden
  rw [WeierstrassCurve.variableChange_a₄]
  simp [translateToOriginTangent]
  linear_combination -hs

@[simp] lemma variableChangePointMap_zero
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℚ) :
    variableChangePointMap W C 0 = 0 :=
  rfl

end

end Scratch.TateZ2xZ10Reduction

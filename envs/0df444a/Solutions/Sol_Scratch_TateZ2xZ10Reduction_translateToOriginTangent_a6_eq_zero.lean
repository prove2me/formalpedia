-- Prove2me | solution 1 for Scratch.TateZ2xZ10Reduction.translateToOriginTangent_a6_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:02:30.094661+00:00
-- url     : https://prove2.me/submissions/e66f81fa-85cf-481e-a64e-46f3fccd5065

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

/-- If `(x₀,y₀)` lies on `W`, the translated curve has constant term zero. -/
theorem _root_.solution
    (W : WeierstrassCurve ℚ) {x₀ y₀ : ℚ}
    (hP : WeierstrassCurve.Affine.Equation W x₀ y₀) :
    ((translateToOriginTangent W x₀ y₀) • W).a₆ = 0 := by
  rw [WeierstrassCurve.variableChange_a₆]
  rw [WeierstrassCurve.Affine.equation_iff] at hP
  simp [translateToOriginTangent]
  nlinarith

@[simp] lemma variableChangePointMap_zero
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℚ) :
    variableChangePointMap W C 0 = 0 :=
  rfl

end

end Scratch.TateZ2xZ10Reduction

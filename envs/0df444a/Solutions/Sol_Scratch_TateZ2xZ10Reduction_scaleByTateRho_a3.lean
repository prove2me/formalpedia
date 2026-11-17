-- Prove2me | solution 1 for Scratch.TateZ2xZ10Reduction.scaleByTateRho_a3
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:02:28.267886+00:00
-- url     : https://prove2.me/submissions/e02ff149-bfbb-4cae-a4d9-7a42c26e0e42

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

lemma scaleByRho_a₃ (W : WeierstrassCurve ℚ) (ρ : ℚ) (hρ : ρ ≠ 0) :
    ((scaleByRho ρ hρ) • W).a₃ = W.a₃ / ρ ^ 3 := by
  rw [WeierstrassCurve.variableChange_a₃]
  simp [scaleByRho, div_eq_mul_inv, inv_pow]
  ring

theorem _root_.solution
    (W : WeierstrassCurve ℚ) (ha₂ : W.a₂ ≠ 0) (ha₃ : W.a₃ ≠ 0) :
    ((scaleByRho (W.a₃ / W.a₂) (div_ne_zero ha₃ ha₂)) • W).a₃ =
      W.a₂ ^ 3 / W.a₃ ^ 2 := by
  rw [scaleByRho_a₃]
  field_simp [ha₂, ha₃]

@[simp] lemma variableChangePointMap_zero
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℚ) :
    variableChangePointMap W C 0 = 0 :=
  rfl

end

end Scratch.TateZ2xZ10Reduction

-- Prove2me | solution 1 for WeierstrassCurve.veluPointMap2_surjective_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/13e74699-cf40-52c9-bdd1-996f1f2b72b9

import Mathlib
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Theorems.Thm_WeierstrassCurve_veluGx_ne_zero_of_two_torsion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_veluPointMap2_surjective_of_isAlgClosed

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace VeluTwoSurjAux

variable {K : Type*} [Field K]

theorem exists_quadratic_root [IsAlgClosed K] (h2 : (2 : K) ≠ 0) (b c : K) :
    ∃ x : K, x ^ 2 + b * x + c = 0 := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (b ^ 2 - 4 * c)
  refine ⟨(s - b) / 2, ?_⟩
  field_simp
  linear_combination -hs

theorem velu2Y_negY {W : WeierstrassCurve K} {x₀ y₀ : K} (hgy : W.veluGy x₀ y₀ = 0)
    {x : K} (y : K) (hx : x ≠ x₀) :
    W.velu2Y x₀ y₀ x (W.toAffine.negY x y)
      = (W.veluQuotient2 x₀ y₀).toAffine.negY (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y) := by
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy
    rw [veluGy, neg_eq_zero] at h
    exact h
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  simp only [velu2Y, velu2X, Affine.negY, veluQuotient2_a₁, veluQuotient2_a₃]
  field_simp
  linear_combination W.veluGx x₀ y₀ * hord

theorem some_ext {W' : Affine K} {x₁ x₂ y₁ y₂ : K} {h₁ : W'.Nonsingular x₁ y₁}
    {h₂ : W'.Nonsingular x₂ y₂} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx
  subst hy
  rfl

end VeluTwoSurjAux

open VeluTwoSurjAux in
theorem solution
    {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    (h2 : (2 : K) ≠ 0) {x₀ y₀ : K} (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) :
    Function.Surjective (veluPointMap2 h2 hQ hgy hΔ) := by
  intro Q'
  cases Q' with
  | zero => exact ⟨0, rfl⟩
  | some u v huv =>

    have ht : W.veluGx x₀ y₀ ≠ 0 := veluGx_ne_zero_of_two_torsion W.isUnit_Δ.ne_zero hQ hgy

    obtain ⟨xs, hxs⟩ := exists_quadratic_root h2 (-(x₀ + u)) (u * x₀ + W.veluGx x₀ y₀)
    have hx : xs ≠ x₀ := by
      rintro rfl
      apply ht
      linear_combination hxs
    have hd : xs - x₀ ≠ 0 := sub_ne_zero.mpr hx
    have hu : W.velu2X x₀ y₀ xs = u := by
      simp only [velu2X]
      field_simp
      linear_combination hxs

    obtain ⟨ys, hys⟩ := exists_quadratic_root h2 (W.a₁ * xs + W.a₃)
      (-(xs ^ 3 + W.a₂ * xs ^ 2 + W.a₄ * xs + W.a₆))
    have hP : W.toAffine.Equation xs ys := by
      rw [Affine.equation_iff]
      linear_combination hys
    have hPns : W.toAffine.Nonsingular xs ys := W.toAffine.equation_iff_nonsingular.mp hP

    have himgEq : (W.veluQuotient2 x₀ y₀).toAffine.Equation
        (W.velu2X x₀ y₀ xs) (W.velu2Y x₀ y₀ xs ys) :=
      (velu2_map_nonsingular h2 hP hQ hgy hx hΔ).left
    rcases Affine.Y_eq_of_X_eq himgEq huv.left hu with hv | hv
    · refine ⟨Point.some xs ys hPns, ?_⟩
      rw [veluPointMap2_some_of_ne h2 hQ hgy hΔ hPns hx]
      exact some_ext hu hv
    · have hPns' : W.toAffine.Nonsingular xs (W.toAffine.negY xs ys) :=
        (Affine.nonsingular_neg ..).mpr hPns
      refine ⟨Point.some xs (W.toAffine.negY xs ys) hPns', ?_⟩
      rw [veluPointMap2_some_of_ne h2 hQ hgy hΔ hPns' hx]
      refine some_ext hu ?_
      rw [velu2Y_negY hgy ys hx, hv, hu, Affine.negY_negY]

end S_WeierstrassCurve_veluPointMap2_surjective_of_isAlgClosed
end P2MW
export P2MW.S_WeierstrassCurve_veluPointMap2_surjective_of_isAlgClosed (solution)

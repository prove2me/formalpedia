-- Prove2me | solution 1 for SphericalFerromagnet.two_theta_isH02CriticalProfile
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-04T18:19:09.71084+00:00
-- url     : https://prove2.me/submissions/e8fca7cb-62ee-42e1-9ae0-512ee36e7e5a

import Definitions.Def_spherical_ferromagnet_profile_defs
import Mathlib

open scoped ContDiff
open Real Set

namespace SphericalFerromagnet

/-- The ODE identity: `2 cot θ - sin 4θ / (2 sin² θ) - 2 sin 2θ = 0`. -/
theorem two_theta_solves_profile_eq : SolvesProfileEq 4 (fun θ => 2 * θ) := by
  intro θ hθ
  have hs : Real.sin θ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne'
  have hd : deriv (fun θ : ℝ => 2 * θ) = fun _ => 2 := by
    funext t
    exact ((hasDerivAt_id t).const_mul (2 : ℝ)).deriv.trans (by simp)
  unfold profileOperator
  rw [hd]
  simp only [deriv_const', zero_add]
  have h4 : (2 : ℝ) * (2 * θ) = 2 * (2 * θ) := rfl
  have e1 : Real.sin (2 * (2 * θ)) = 2 * (2 * Real.sin θ * Real.cos θ) *
      (1 - 2 * Real.sin θ ^ 2) := by
    rw [Real.sin_two_mul, Real.sin_two_mul, Real.cos_two_mul, Real.cos_sq']
    ring
  have e2 : (2 : ℝ) * (2 * θ) - 2 * θ = 2 * θ := by ring
  rw [e1, e2, Real.sin_two_mul]
  field_simp
  ring

/-- Explicit polynomial-over-`|x|²` form of the field induced by `h = 2θ`. -/
noncomputable def twoThetaField (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![2 * x 0 * x 2 / (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2),
    2 * x 1 * x 2 / (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2),
    2 * x 2 ^ 2 / (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) - 1]

lemma normSq_ne_zero {x : Fin 3 → ℝ} (hx : x ≠ 0) : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 ≠ 0 := by
  intro hS
  apply hx
  have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  have h2 : x 2 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  funext i
  fin_cases i <;> simp [h0, h1, h2]

lemma twoThetaField_contDiffOn :
    ContDiffOn ℝ ∞ twoThetaField {x : Fin 3 → ℝ | x ≠ 0} := by
  have hS : ContDiff ℝ ∞ (fun x : Fin 3 → ℝ => x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by fun_prop
  have hne : ∀ x ∈ {x : Fin 3 → ℝ | x ≠ 0}, x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 ≠ 0 :=
    fun x hx => normSq_ne_zero hx
  rw [contDiffOn_pi]
  intro i
  fin_cases i
  · simp only [twoThetaField]
    exact (ContDiff.contDiffOn (by fun_prop)).div hS.contDiffOn hne
  · simp only [twoThetaField]
    exact (ContDiff.contDiffOn (by fun_prop)).div hS.contDiffOn hne
  · simp only [twoThetaField]
    exact ((ContDiff.contDiffOn (by fun_prop)).div hS.contDiffOn hne).sub contDiffOn_const

lemma inducedField_two_theta {x : Fin 3 → ℝ} (hx : x ≠ 0) :
    inducedField (fun θ => 2 * θ) x = twoThetaField x := by
  set S := x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 with hSdef
  have hS : S ≠ 0 := normSq_ne_zero hx
  have hSpos : 0 < S := lt_of_le_of_ne (by positivity) (Ne.symm hS)
  set ρ := Real.sqrt S with hρ
  have hρpos : 0 < ρ := Real.sqrt_pos.mpr hSpos
  have hρsq : ρ ^ 2 = S := Real.sq_sqrt hSpos.le
  set t := x 2 / ρ with ht
  have ht2 : t ^ 2 = x 2 ^ 2 / S := by rw [ht, div_pow, hρsq]
  have htle : t ^ 2 ≤ 1 := by
    rw [ht2, div_le_one hSpos]; nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  have htm : -1 ≤ t := by nlinarith [sq_nonneg (t + 1)]
  have htM : t ≤ 1 := by nlinarith [sq_nonneg (t - 1)]
  have hcos : Real.cos (2 * Real.arccos t) = 2 * x 2 ^ 2 / S - 1 := by
    rw [Real.cos_two_mul, Real.cos_arccos htm htM, ht2]; ring
  set r := Real.sqrt (x 0 ^ 2 + x 1 ^ 2) with hr
  unfold inducedField
  simp only []
  rw [← hSdef, ← hρ, ← ht, ← hr]
  by_cases hr0 : r = 0
  · rw [if_pos hr0]
    have hq : x 0 ^ 2 + x 1 ^ 2 = 0 := by
      have := Real.sqrt_eq_zero'.mp hr0
      linarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    have hS' : S = x 2 ^ 2 := by rw [hSdef, h0, h1]; ring
    funext i
    fin_cases i <;> simp [twoThetaField, h0, h1, hcos, hS']
  · rw [if_neg hr0]
    have hrpos : 0 < r := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr0)
    have hsin : Real.sin (Real.arccos t) = r / ρ := by
      rw [Real.sin_arccos]
      have : 1 - t ^ 2 = (x 0 ^ 2 + x 1 ^ 2) / S := by
        rw [ht2]; field_simp; rw [hSdef]; ring
      rw [this, Real.sqrt_div' _ hSpos.le]
    have hsin2 : Real.sin (2 * Real.arccos t) = 2 * (r / ρ) * t := by
      rw [Real.sin_two_mul, hsin, Real.cos_arccos htm htM]
    funext i
    fin_cases i
    · simp only [twoThetaField, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [hsin2, ← hSdef, ← hρsq, ht]; field_simp
    · simp only [twoThetaField, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_zero]
      rw [hsin2, ← hSdef, ← hρsq, ht]; field_simp
    · simp [twoThetaField, hcos, ← hSdef]

theorem two_theta_inducesSmoothMap : InducesSmoothMap (fun θ => 2 * θ) := by
  unfold InducesSmoothMap
  exact twoThetaField_contDiffOn.congr (fun x hx => inducedField_two_theta hx)

theorem two_theta_isH02CriticalProfile' : IsH02CriticalProfile 4 (fun θ => 2 * θ) := by
  refine ⟨?_, two_theta_inducesSmoothMap, two_theta_solves_profile_eq, by simp, by ring, ?_⟩
  · exact (contDiff_const.mul contDiff_id).contDiffOn
  · intro θ _; ring

end SphericalFerromagnet

open SphericalFerromagnet

theorem solution : IsH02CriticalProfile 4 (fun θ => 2 * θ) :=
  two_theta_isH02CriticalProfile'

-- Prove2me | solution 1 for OnlineBeckFiala.eq_13
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:11:12.49334+00:00
-- url     : https://prove2.me/submissions/69b79d62-b6cd-4b1b-815c-132f34a5a9eb

import Mathlib
import Definitions.Def_OnlineBeckFiala_W
import Theorems.Thm_OnlineBeckFiala_A_derivatives

section
namespace OnlineBeckFiala

namespace Dev.Eq13

lemma one_le_A (η y : ℝ) (hη : 0 < η) (hy : y ∈ Set.Ioo (-1 : ℝ) 1) : 1 ≤ A η y := by
  have hx : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
  unfold A
  apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx (by nlinarith [sq_nonneg y])
  have : 0 < 2 / η := by positivity
  rw [neg_div]; linarith

lemma u_second (η : ℝ) (hη : 0 < η) (y : ℝ) (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    iteratedDeriv 2 (u η) y =
      u η y * ((deriv (A η) y) ^ 2 + iteratedDeriv 2 (A η) y) := by
  have hnhds : Set.Ioo (-1 : ℝ) 1 ∈ nhds y := Ioo_mem_nhds hy.1 hy.2
  have hAd : ∀ z ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt (A η) (4 * z / η * A η z ^ (1 + η / 2)) z :=
    fun z hz => (A_derivatives η hη).1 z hz
  have hAdiff : DifferentiableAt ℝ (A η) y := (hAd y hy).differentiableAt
  have hA1 := one_le_A η y hη hy
  have hBdiff : DifferentiableAt ℝ (fun z => 4 * z / η * A η z ^ (1 + η / 2)) y := by
    have h1 : DifferentiableAt ℝ (fun z : ℝ => 4 * z / η) y := by fun_prop
    exact h1.mul (hAdiff.rpow_const (Or.inl (by linarith)))
  have hev : deriv (A η) =ᶠ[nhds y] (fun z => 4 * z / η * A η z ^ (1 + η / 2)) := by
    filter_upwards [hnhds] with z hz
    exact (hAd z hz).deriv
  have hdA' : HasDerivAt (deriv (A η)) (deriv (deriv (A η)) y) y := by
    have : DifferentiableAt ℝ (deriv (A η)) y := (hev.differentiableAt_iff).2 hBdiff
    exact this.hasDerivAt
  have hAy : HasDerivAt (A η) (deriv (A η) y) y := hAdiff.hasDerivAt
  have hev2 : deriv (u η) =ᶠ[nhds y] (fun z => Real.exp (A η z) * deriv (A η) z) := by
    filter_upwards [hnhds] with z hz
    have hz' : HasDerivAt (A η) (deriv (A η) z) z := ((hAd z hz).differentiableAt).hasDerivAt
    exact (hz'.exp).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_one,
    hev2.deriv_eq]
  have this : HasDerivAt (fun z => Real.exp (A η z) * deriv (A η) z)
      (Real.exp (A η y) * deriv (A η) y * deriv (A η) y +
        Real.exp (A η y) * deriv (deriv (A η)) y) y := (hAy.exp).mul hdA'
  rw [this.deriv]
  unfold u
  ring

end Dev.Eq13

theorem chk_eq_13 (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
      0 ≤ iteratedDeriv 2 (u η) y ∧
      iteratedDeriv 2 (u η) y = u η y * ((deriv (A η) y) ^ 2 + iteratedDeriv 2 (A η) y) ∧
      iteratedDeriv 2 (u η) y ≤ C * u η y * (Real.log (u η y)) ^ (2 + η) := by
  obtain ⟨C, hC, hb⟩ := (A_derivatives η hη).2
  refine ⟨16 / η ^ 2 + C, by positivity, fun y hy => ?_⟩
  have hform := Dev.Eq13.u_second η hη y hy
  have hA1 := Dev.Eq13.one_le_A η y hη hy
  obtain ⟨hn, hle⟩ := hb y hy
  have hd : deriv (A η) y = 4 * y / η * A η y ^ (1 + η / 2) :=
    ((A_derivatives η hη).1 y hy).deriv
  have hlog : Real.log (u η y) = A η y := by unfold u; exact Real.log_exp _
  have hupos : 0 < u η y := by unfold u; exact Real.exp_pos _
  set a := A η y with ha
  have ha0 : 0 < a := by linarith
  have hy2 : y ^ 2 ≤ 1 := by nlinarith [hy.1, hy.2]
  refine ⟨?_, hform, ?_⟩
  · rw [hform]; exact mul_nonneg hupos.le (by positivity)
  · rw [hform, hlog]
    have hsq : (deriv (A η) y) ^ 2 = (4 * y / η) ^ 2 * a ^ (2 + η) := by
      have e : (a ^ (1 + η / 2)) ^ 2 = a ^ (2 + η) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
        congr 1; push_cast; ring
      rw [hd, mul_pow, e]
    have hmono : a ^ (1 + η) ≤ a ^ (2 + η) :=
      Real.rpow_le_rpow_of_exponent_le hA1 (by linarith)
    have hp0 : 0 < a ^ (2 + η) := Real.rpow_pos_of_pos ha0 _
    have hc : (4 * y / η) ^ 2 ≤ 16 / η ^ 2 := by
      rw [div_pow, mul_pow]
      have : (4 : ℝ) ^ 2 * y ^ 2 ≤ 16 := by nlinarith
      exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    have h2 : (deriv (A η) y) ^ 2 + iteratedDeriv 2 (A η) y ≤ (16 / η ^ 2 + C) * a ^ (2 + η) := by
      rw [hsq]
      nlinarith [mul_le_mul_of_nonneg_right hc hp0.le, mul_le_mul_of_nonneg_left hmono hC.le]
    calc u η y * ((deriv (A η) y) ^ 2 + iteratedDeriv 2 (A η) y)
        ≤ u η y * ((16 / η ^ 2 + C) * a ^ (2 + η)) := mul_le_mul_of_nonneg_left h2 hupos.le
      _ = _ := by ring

end OnlineBeckFiala

end

theorem solution : type_of% @OnlineBeckFiala.chk_eq_13 := @OnlineBeckFiala.chk_eq_13

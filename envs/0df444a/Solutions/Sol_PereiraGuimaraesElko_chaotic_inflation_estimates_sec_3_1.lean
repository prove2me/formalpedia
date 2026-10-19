-- Prove2me | solution 1 for PereiraGuimaraesElko.chaotic_inflation_estimates_sec_3_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:26:26.567304+00:00
-- url     : https://prove2.me/submissions/6bd4b449-de63-4de4-8edd-d3c13c6cc6bc

import Mathlib

theorem solution (κ Λ σ v₀ Φi Hi2 : ℝ) (V : ℝ → ℝ)
    (hκ : κ ^ 2 = 8 * Real.pi)
    (hΛ : Λ = 5e-6) (hσ : σ = 1) (hv₀ : v₀ = 0) (hΦi : Φi = 2.1)
    (hV : ∀ Φ, V Φ = v₀ + Λ ^ 4 * (1 - Φ ^ 2 / σ ^ 2) ^ 2)
    (hHi2 : Hi2 = κ ^ 2 / 3 * (1 + κ ^ 2 * Φi ^ 2 / 8) * V Φi) :
    |Hi2 - 9.04e-19| ≤ 0.05 * 9.04e-19 ∧
    |1 / (Real.sqrt Hi2 * 1.86e43) - 5.7e-35| ≤ 0.05 * 5.7e-35 ∧
    |V Φi - 7.2e-21| ≤ 0.05 * 7.2e-21 ∧
    |1 / κ ^ 2 * (deriv V Φi / V Φi) ^ 2 - 0.24| ≤ 0.05 * 0.24 ∧
    |abs (1 / κ ^ 2 * deriv (deriv V) Φi / ((1 + κ ^ 2 * Φi ^ 2 / 8) * V Φi)) - 0.011|
      ≤ 0.05 * 0.011 ∧
    |Real.sqrt 2 * (2 * Λ ^ 2 / σ) - 7.1e-11| ≤ 0.05 * 7.1e-11 ∧
    |Real.sqrt 2 * (2 * Λ ^ 2 / σ) * 1.22e19 - 8.6e8| ≤ 0.05 * 8.6e8 ∧
    4 * Λ ^ 4 / σ ^ 4 = 2.5e-21 := by
  subst hΛ hσ hv₀ hΦi
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  have hVf : V = fun Φ => (5e-6 : ℝ) ^ 4 * (1 - Φ ^ 2) ^ 2 := by
    funext Φ; rw [hV]; ring
  have hd1 : ∀ x, HasDerivAt V ((5e-6 : ℝ) ^ 4 * (-4 * x + 4 * x ^ 3)) x := by
    intro x
    rw [hVf]
    have e : (fun Φ : ℝ => (5e-6 : ℝ) ^ 4 * (1 - Φ ^ 2) ^ 2) =
        fun Φ => (5e-6 : ℝ) ^ 4 * (1 - 2 * Φ ^ 2 + Φ ^ 4) := by funext Φ; ring
    rw [e]
    have := (((hasDerivAt_pow 2 x).const_mul 2).const_sub 1 |>.add (hasDerivAt_pow 4 x)).const_mul
      ((5e-6 : ℝ) ^ 4)
    refine this.congr_deriv ?_; push_cast; ring
  have hd1' : deriv V = fun x => (5e-6 : ℝ) ^ 4 * (-4 * x + 4 * x ^ 3) :=
    funext fun x => (hd1 x).deriv
  have hd2 : ∀ x, HasDerivAt (deriv V) ((5e-6 : ℝ) ^ 4 * (-4 + 12 * x ^ 2)) x := by
    intro x
    rw [hd1']
    have := (((hasDerivAt_id x).const_mul (-4)).add ((hasDerivAt_pow 3 x).const_mul 4)).const_mul
      ((5e-6 : ℝ) ^ 4)
    refine this.congr_deriv ?_; push_cast; ring
  have hVi : V 2.1 = 7.2675625e-21 := by rw [hVf]; norm_num
  have hVd : deriv V 2.1 = (5e-6 : ℝ) ^ 4 * (-4 * 2.1 + 4 * 2.1 ^ 3) := (hd1 _).deriv
  have hVdd : deriv (deriv V) 2.1 = (5e-6 : ℝ) ^ 4 * (-4 + 12 * 2.1 ^ 2) := (hd2 _).deriv
  have hH : Hi2 = 8 * Real.pi / 3 * (1 + Real.pi * 4.41) * 7.2675625e-21 := by
    rw [hHi2, hκ, hVi]; ring
  have hHlo : 9.0e-19 ≤ Hi2 := by rw [hH]; nlinarith
  have hHhi : Hi2 ≤ 9.1e-19 := by rw [hH]; nlinarith
  have hs2 : Real.sqrt 2 < 1.4143 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs2' : 1.4142 < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hsH1 : 9.48e-10 ≤ Real.sqrt Hi2 := by
    rw [show (9.48e-10 : ℝ) = Real.sqrt (9.48e-10 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hsH2 : Real.sqrt Hi2 ≤ 9.54e-10 := by
    rw [show (9.54e-10 : ℝ) = Real.sqrt (9.54e-10 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [abs_sub_le_iff]; constructor <;> nlinarith
  · have hpos : 0 < Real.sqrt Hi2 * 1.86e43 := by positivity
    have b1 : 1 / (Real.sqrt Hi2 * 1.86e43) ≤ 5.7e-35 := by
      rw [div_le_iff₀ hpos]; nlinarith
    have b2 : 5.6e-35 ≤ 1 / (Real.sqrt Hi2 * 1.86e43) := by
      rw [le_div_iff₀ hpos]; nlinarith
    rw [abs_sub_le_iff]; constructor <;> linarith
  · rw [hVi]; norm_num [abs_le]
  · rw [hVd, hVi, hκ]
    rw [abs_sub_le_iff]; constructor
    · rw [sub_le_iff_le_add]
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; norm_num; nlinarith
    · rw [sub_le_comm]
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]; norm_num; nlinarith
  · rw [hVdd, hVi, hκ]
    have hval : 0 < 1 / (8 * Real.pi) * ((5e-6 : ℝ) ^ 4 * (-4 + 12 * 2.1 ^ 2)) /
        ((1 + 8 * Real.pi * 2.1 ^ 2 / 8) * 7.2675625e-21) := by positivity
    rw [abs_of_pos hval, abs_sub_le_iff]; constructor
    · rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]; field_simp; norm_num; nlinarith
    · rw [sub_le_comm, le_div_iff₀ (by positivity)]; field_simp; norm_num; nlinarith
  · rw [abs_sub_le_iff]; constructor <;> norm_num <;> nlinarith
  · rw [abs_sub_le_iff]; constructor <;> norm_num <;> nlinarith
  · norm_num

-- Prove2me | solution 1 for OnlineCombOpt.Exp2LB.appA_eta_optimization
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:25:19.829045+00:00
-- url     : https://prove2.me/submissions/f2727591-56f3-4ec3-948f-df23c1b048a5

import Mathlib
set_option autoImplicit false

lemma oce_tanh_eq (x : ℝ) : Real.tanh x = (Real.exp (2 * x) - 1) / (Real.exp (2 * x) + 1) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have h2 : Real.exp (2 * x) = Real.exp x * Real.exp x := by
    rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x
  have hp : 0 < Real.exp x := Real.exp_pos x
  rw [h2, h3]
  field_simp

lemma oce_tanh_ge_one (x : ℝ) (hx : 1 ≤ x) : (64 : ℝ) / 100 ≤ Real.tanh x := by
  rw [oce_tanh_eq]
  have h1 : Real.exp 2 ≤ Real.exp (2 * x) := Real.exp_le_exp.2 (by linarith)
  have h2 : (7 : ℝ) ≤ Real.exp 2 := by
    have := Real.exp_one_gt_d9
    have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    rw [e]; nlinarith
  have hpos : 0 < Real.exp (2 * x) + 1 := by positivity
  rw [le_div_iff₀ hpos]
  nlinarith

lemma oce_tanh_ge_half (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x / 2 ≤ Real.tanh x := by
  rw [oce_tanh_eq]
  have hy : 0 ≤ 2 * x := by linarith
  have hE := Real.sum_le_exp_of_nonneg hy 4
  simp [Finset.sum_range_succ, Nat.factorial] at hE
  have hpos : 0 < Real.exp (2 * x) + 1 := by positivity
  rw [le_div_iff₀ hpos]
  generalize Real.exp (2 * x) = E at *
  nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0, mul_nonneg (mul_nonneg h0 h0) (sub_nonneg.2 h1),
    mul_nonneg h0 (sub_nonneg.2 h1)]

theorem solution (n d : ℕ) (η : ℝ) (hη : 0 < η) :
    min ((4 : ℝ) / 100 * n * d) ((1 : ℝ) / 100 * d * Real.sqrt d * Real.sqrt n) ≤
      max ((n : ℝ) * d / 16 * Real.tanh (η * d / 8))
        (min ((d : ℝ) * Real.log 2 / (12 * η)) ((n : ℝ) * d / 12)) := by
  have hN0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hD0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hlog : (69 : ℝ) / 100 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp only [Nat.cast_zero, mul_zero, zero_mul, Real.sqrt_zero, min_self, zero_div, Real.tanh_zero]
    simp
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Nat.cast_zero, mul_zero, zero_mul, Real.sqrt_zero, min_self, zero_div]
    exact le_max_of_le_right (le_min (by positivity) le_rfl)
  have hNp : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hDp : (0 : ℝ) < d := Nat.cast_pos.2 hd
  set N : ℝ := (n : ℝ) with hNdef
  set D : ℝ := (d : ℝ) with hDdef
  obtain ⟨r, hr, hrD⟩ : ∃ r : ℝ, 0 < r ∧ D = r ^ 2 := ⟨Real.sqrt D, Real.sqrt_pos.2 hDp, (Real.sq_sqrt hD0).symm⟩
  obtain ⟨q, hq, hqN⟩ : ∃ q : ℝ, 0 < q ∧ N = q ^ 2 := ⟨Real.sqrt N, Real.sqrt_pos.2 hNp, (Real.sq_sqrt hN0).symm⟩
  have hsD : Real.sqrt D = r := by rw [hrD, Real.sqrt_sq hr.le]
  have hsN : Real.sqrt N = q := by rw [hqN, Real.sqrt_sq hq.le]
  rw [hsD, hsN]
  set m := min ((4 : ℝ) / 100 * N * D) ((1 : ℝ) / 100 * D * r * q) with hm
  have hm1 : m ≤ 4 / 100 * N * D := min_le_left _ _
  have hm2 : m ≤ 1 / 100 * D * r * q := min_le_right _ _
  by_cases hb : m ≤ D * Real.log 2 / (12 * η)
  · refine le_max_of_le_right (le_min hb ?_)
    have : 0 ≤ N * D := by positivity
    nlinarith
  · push Not at hb
    refine le_max_of_le_left ?_
    have hb2 : D * Real.log 2 / (12 * η) < 1 / 100 * D * r * q := lt_of_lt_of_le hb hm2
    rw [div_lt_iff₀ (by positivity)] at hb2
    -- η * r * q > 5.75
    have hkey : (575 : ℝ) / 100 < η * r * q := by
      rw [hrD] at hb2
      have h1 : r ^ 2 * (69 / 100) < r ^ 2 * Real.log 2 := by
        apply mul_lt_mul_of_pos_left hlog (by positivity)
      have : r ^ 2 * (69 / 100) < 1 / 100 * r ^ 2 * r * q * (12 * η) := by linarith
      have hr2 : 0 < r ^ 2 := by positivity
      by_contra hcon
      push Not at hcon
      have : 1 / 100 * r ^ 2 * r * q * (12 * η) = r ^ 2 * (12 / 100 * (η * r * q)) := by ring
      nlinarith
    by_cases hx : 1 ≤ η * D / 8
    · have := oce_tanh_ge_one _ hx
      have h0 : 0 ≤ N * D := by positivity
      calc m ≤ 4 / 100 * N * D := hm1
        _ ≤ N * D / 16 * (64 / 100) := by nlinarith
        _ ≤ N * D / 16 * Real.tanh (η * D / 8) := by gcongr
    · push Not at hx
      have := oce_tanh_ge_half (η * D / 8) (by positivity) hx.le
      calc m ≤ 1 / 100 * D * r * q := hm2
        _ ≤ N * D / 16 * ((η * D / 8) / 2) := by
          rw [hrD, hqN]
          have : 1 / 100 * r ^ 2 * r * q ≤ q ^ 2 * r ^ 2 / 16 * (η * r ^ 2 / 8 / 2) := by
            have e : q ^ 2 * r ^ 2 / 16 * (η * r ^ 2 / 8 / 2) = (r ^ 3 * q) * (η * r * q / 256) := by ring
            have e2 : 1 / 100 * r ^ 2 * r * q = (r ^ 3 * q) * (1 / 100) := by ring
            rw [e, e2]
            have : 0 < r ^ 3 * q := by positivity
            apply mul_le_mul_of_nonneg_left _ this.le
            linarith
          exact this
        _ ≤ N * D / 16 * Real.tanh (η * D / 8) := by gcongr

-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.overlap_three_exponential_errors
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:36:24.657124+00:00
-- url     : https://prove2.me/submissions/ceb8104a-389c-411f-add7-b2b300c01c2f

import Mathlib
set_option autoImplicit false

theorem solution (A B C a b c : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∃ r : ℝ, 0 < r ∧ ∃ N : ℕ, ∀ n ≥ N,
      A * Real.exp (-a * n) + B * Real.exp (-b * n) + C * Real.exp (-c * n)
        ≤ Real.exp (-r * n) := by
  let m := min a (min b c)
  let r := m / 2
  have hm : 0 < m := lt_min ha (lt_min hb hc)
  have hr : 0 < r := by dsimp [r]; linarith
  have hma : m ≤ a := min_le_left _ _
  have hmb : m ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have hmc : m ≤ c := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨N,hN⟩ := exists_nat_gt ((A+B+C)/r)
  refine ⟨r,hr,N,?_⟩
  intro n hn
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hNn : (N:ℝ) ≤ n := by exact_mod_cast hn
  have hlarge : A+B+C ≤ r*n := by
    have hh : A+B+C < r*N := by simpa only [mul_comm] using (div_lt_iff₀ hr).mp hN
    nlinarith
  have he (x : ℝ) (hx : m ≤ x) : Real.exp (-x*n) ≤ Real.exp (-m*n) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) hn0]
  have hsum : A * Real.exp (-a*n) + B * Real.exp (-b*n) + C * Real.exp (-c*n)
      ≤ (A+B+C) * Real.exp (-m*n) := by
    have h1 := mul_le_mul_of_nonneg_left (he a hma) hA
    have h2 := mul_le_mul_of_nonneg_left (he b hmb) hB
    have h3 := mul_le_mul_of_nonneg_left (he c hmc) hC
    nlinarith
  have hexp : A+B+C ≤ Real.exp (r*n) := by
    have h := Real.add_one_le_exp (r*n)
    linarith
  have hproduct := mul_le_mul_of_nonneg_right hexp (le_of_lt (Real.exp_pos (-m*n)))
  have hexact : Real.exp (r*n) * Real.exp (-m*n) = Real.exp (-r*n) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [r]
    ring
  exact hsum.trans (by simpa only [hexact] using hproduct)

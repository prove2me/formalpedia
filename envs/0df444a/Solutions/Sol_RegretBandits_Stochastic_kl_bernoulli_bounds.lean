-- Prove2me | solution 1 for RegretBandits.Stochastic.kl_bernoulli_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T21:07:12.175956+00:00
-- url     : https://prove2.me/submissions/deacb5db-23f9-404c-a404-8e74be7a4bd3

import Mathlib
import Definitions.Def_RegretBandits_Stochastic_klBernoulli

set_option autoImplicit false

namespace KlBernD50919cc

lemma negLog_ge (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1) : 2 * t ^ 2 ≤ -Real.log (1 - t) := by
  let f : ℝ → ℝ := fun x => -Real.log (1 - x) - 2 * x ^ 2
  have hd : ∀ x : ℝ, x < 1 → HasDerivAt f (1 / (1 - x) - 4 * x) x := by
    intro x hx
    have e1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    have e2 := e1.log (by linarith)
    have e3 := (hasDerivAt_pow 2 x).const_mul 2
    exact ((e2.neg).sub e3).congr_deriv (by norm_num <;> ring)
  have hmono : MonotoneOn f (Set.Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
    · intro x hx
      exact (hd x (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x (by linarith [hx.2])).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x (by linarith [hx.2])).deriv]
      have hx1 : 0 < 1 - x := by linarith [hx.2]
      have e : 1 / (1 - x) - 4 * x = (1 - 2 * x) ^ 2 / (1 - x) := by
        field_simp
        ring
      rw [e]
      exact div_nonneg (sq_nonneg _) hx1.le
  have := hmono ⟨le_refl 0, h0⟩ ⟨h0, le_refl t⟩ h0
  simp [f] at this
  linarith

lemma interior_case (p q : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    2 * (p - q) ^ 2 ≤ RegretBandits.Stochastic.klBern p q := by
  let G : ℝ → ℝ := fun x => -p * Real.log x - (1 - p) * Real.log (1 - x) - 2 * (p - x) ^ 2
  have hd : ∀ x : ℝ, 0 < x → x < 1 →
      HasDerivAt G (-p / x + (1 - p) / (1 - x) + 4 * (p - x)) x := by
    intro x hx0 hx1
    have e1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    have e2 := e1.log (by linarith)
    have e0 := (Real.hasDerivAt_log (ne_of_gt hx0)).const_mul (-p)
    have e4 : HasDerivAt (fun x : ℝ => p - x) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub p
    have e3 := (e4.pow 2).const_mul 2
    exact ((e0.sub (e2.const_mul (1 - p))).sub e3).congr_deriv (by norm_num <;> ring)
  have hG' : ∀ x : ℝ, 0 < x → x < 1 →
      -p / x + (1 - p) / (1 - x) + 4 * (p - x) = (x - p) * (1 - 4 * x * (1 - x)) / (x * (1 - x)) := by
    intro x hx0 hx1
    have : (1 - x) ≠ 0 := by linarith
    have : x ≠ 0 := by linarith
    field_simp
    ring
  have hkl : ∀ x : ℝ, 0 < x → x < 1 →
      RegretBandits.Stochastic.klBern p x - 2 * (p - x) ^ 2
        = p * Real.log p + (1 - p) * Real.log (1 - p) + G x := by
    intro x hx0 hx1
    simp only [RegretBandits.Stochastic.klBern, G]
    rw [Real.log_div (by linarith) (by linarith), Real.log_div (by linarith) (by linarith)]
    ring
  have hpp : RegretBandits.Stochastic.klBern p p - 2 * (p - p) ^ 2 = 0 := by
    simp [RegretBandits.Stochastic.klBern, div_self (ne_of_gt hp0),
      div_self (show (1 - p) ≠ 0 by linarith)]
  have key : G p ≤ G q := by
    rcases le_total p q with hpq | hqp
    · have hmono : MonotoneOn G (Set.Icc p q) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc p q)
        · intro x hx
          exact (hd x (by linarith [hx.1]) (by linarith [hx.2])).continuousAt.continuousWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          exact (hd x (by linarith [hx.1]) (by linarith [hx.2])).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          have hx0 : 0 < x := by linarith [hx.1]
          have hx1 : x < 1 := by linarith [hx.2]
          rw [(hd x hx0 hx1).deriv, hG' x hx0 hx1]
          apply div_nonneg
          · apply mul_nonneg (by linarith [hx.1])
            nlinarith [sq_nonneg (2 * x - 1)]
          · nlinarith
      exact hmono ⟨le_refl p, hpq⟩ ⟨hpq, le_refl q⟩ hpq
    · have hanti : AntitoneOn G (Set.Icc q p) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc q p)
        · intro x hx
          exact (hd x (by linarith [hx.1]) (by linarith [hx.2])).continuousAt.continuousWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          exact (hd x (by linarith [hx.1]) (by linarith [hx.2])).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          have hx0 : 0 < x := by linarith [hx.1]
          have hx1 : x < 1 := by linarith [hx.2]
          rw [(hd x hx0 hx1).deriv, hG' x hx0 hx1]
          apply div_nonpos_of_nonpos_of_nonneg
          · apply mul_nonpos_of_nonpos_of_nonneg (by linarith [hx.2])
            nlinarith [sq_nonneg (2 * x - 1)]
          · nlinarith
      exact hanti ⟨le_refl q, hqp⟩ ⟨hqp, le_refl p⟩ hqp
  have h1 := hkl q hq0 hq1
  have h2 := hkl p hp0 hp1
  linarith

lemma lower (p q : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    2 * (p - q) ^ 2 ≤ RegretBandits.Stochastic.klBern p q := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hq0, hq1⟩ := hq
  rcases eq_or_lt_of_le hp0 with h | h
  · subst h
    have := negLog_ge q hq0.le hq1
    simp only [RegretBandits.Stochastic.klBern, zero_mul, zero_add, sub_zero, one_mul, one_div,
      Real.log_inv]
    nlinarith
  rcases eq_or_lt_of_le hp1 with h' | h'
  · subst h'
    have := negLog_ge (1 - q) (by linarith) (by linarith)
    simp only [RegretBandits.Stochastic.klBern, sub_self, zero_mul, add_zero, one_mul, one_div,
      Real.log_inv]
    have e : (1 : ℝ) - (1 - q) = q := by ring
    rw [e] at this
    nlinarith
  exact interior_case p q h h' hq0 hq1

lemma upper (p q : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    RegretBandits.Stochastic.klBern p q ≤ (p - q) ^ 2 / (q * (1 - q)) := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hq0, hq1⟩ := hq
  have hq1' : 0 < 1 - q := by linarith
  have a : p * Real.log (p / q) ≤ p * (p / q - 1) := by
    rcases eq_or_lt_of_le hp0 with h | h
    · subst h; simp
    · exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos h hq0)) hp0
  have b : (1 - p) * Real.log ((1 - p) / (1 - q)) ≤ (1 - p) * ((1 - p) / (1 - q) - 1) := by
    rcases eq_or_lt_of_le (show 0 ≤ 1 - p by linarith) with h | h
    · rw [← h]; simp
    · exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos h hq1')) h.le
  have e : p * (p / q - 1) + (1 - p) * ((1 - p) / (1 - q) - 1) = (p - q) ^ 2 / (q * (1 - q)) := by
    field_simp
    ring
  unfold RegretBandits.Stochastic.klBern
  linarith

end KlBernD50919cc

open RegretBandits.Stochastic in
theorem solution (p q : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    2 * (p - q) ^ 2 ≤ klBern p q ∧ klBern p q ≤ (p - q) ^ 2 / (q * (1 - q)) := by
  exact ⟨KlBernD50919cc.lower p q hp hq, KlBernD50919cc.upper p q hp hq⟩

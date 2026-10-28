-- Prove2me | solution 1 for RobustSPA.FixedReserve.optimal_reserve
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T17:42:33.56696+00:00
-- url     : https://prove2.me/submissions/f0fa0ac0-8abc-497f-b0ea-66580efacef5

import Mathlib
import Definitions.Def_RobustSPA_FixedReserve_Setting

open MeasureTheory

namespace FROptR

/-- strict Bernoulli -/
lemma bern_strict (x : ℝ) (hx : -1 < x) (hx0 : x ≠ 0) (j : ℕ) (hj : 1 ≤ j) :
    1 + ((j + 1 : ℕ) : ℝ) * x < (1 + x) ^ (j + 1) := by
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ x by linarith) j
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hx2 : 0 < x ^ 2 := by positivity
  rw [pow_succ]
  have h1x : 0 < 1 + x := by linarith
  calc 1 + ((j + 1 : ℕ) : ℝ) * x < (1 + j * x) * (1 + x) := by push_cast; nlinarith
    _ ≤ (1 + x) ^ j * (1 + x) := mul_le_mul_of_nonneg_right hb h1x.le

/-- `t^{n-1} ≤ s^n` with `s = ((n-1) t + 1)/n`, strict unless `t = 1`. Here `n = k + 2`. -/
lemma amgm (k : ℕ) (N t : ℝ) (hN : N = (k : ℝ) + 2) (ht : 0 < t) :
    t ^ (k + 1) ≤ (((N - 1) * t + 1) / N) ^ (k + 2) ∧
      (t ≠ 1 → t ^ (k + 1) < (((N - 1) * t + 1) / N) ^ (k + 2)) := by
  have hNpos : 0 < N := by rw [hN]; positivity
  set x : ℝ := (1 - t) / (N * t) with hx
  have hs : ((N - 1) * t + 1) / N = t * (1 + x) := by
    rw [hx]; field_simp; ring
  have hxgt : -1 < x := by
    rw [hx, lt_div_iff₀ (by positivity)]
    have : (2 : ℝ) ≤ N := by rw [hN]; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
    nlinarith
  have hkey : t ^ (k + 2) * (1 + ((k + 2 : ℕ) : ℝ) * x) = t ^ (k + 1) := by
    have : ((k + 2 : ℕ) : ℝ) = N := by rw [hN]; push_cast; ring
    rw [this, hx, pow_succ]
    field_simp
    ring
  have htp : 0 < t ^ (k + 2) := by positivity
  rw [hs, mul_pow]
  constructor
  · rw [← hkey]
    exact mul_le_mul_of_nonneg_left (one_add_mul_le_pow (by linarith) _) htp.le
  · intro ht1
    have hx0 : x ≠ 0 := by
      rw [hx]; exact div_ne_zero (sub_ne_zero.mpr (Ne.symm ht1)) (by positivity)
    rw [← hkey]
    exact mul_lt_mul_of_pos_left (bern_strict x hxgt hx0 (k + 1) (by omega)) htp

lemma V_le_half (k : ℕ) (N : ℝ) (hN : N = (k : ℝ) + 2) : (N / (N + 1)) ^ (k + 2) ≤ 1 / 2 := by
  have hNpos : 0 < N := by rw [hN]; positivity
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / N by
    have : 0 < 1 / N := by positivity
    linarith) (k + 2)
  have hc : ((k + 2 : ℕ) : ℝ) * (1 / N) = 1 := by rw [hN]; push_cast; field_simp
  rw [hc] at hb
  have he : N / (N + 1) = 1 / (1 + 1 / N) := by field_simp
  rw [he, div_pow, one_pow]
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

end FROptR

open FROptR RobustSPA.FixedReserve in
theorem solution (n : ℕ) (hn : 0 < n) :
    IsLeast (wcFixed n '' Set.Icc 0 1) (((n : ℝ) / (n + 1)) ^ n) ∧
    wcFixed n (1 / (n + 1)) = ((n : ℝ) / (n + 1)) ^ n ∧
    ∀ r ∈ Set.Icc (0 : ℝ) 1, wcFixed n r = ((n : ℝ) / (n + 1)) ^ n → r = 1 / (n + 1) := by
  -- the two facts: lower bound with uniqueness of equality, and value at 1/(n+1)
  suffices H : (∀ r ∈ Set.Icc (0 : ℝ) 1, ((n : ℝ) / (n + 1)) ^ n ≤ wcFixed n r ∧
      (wcFixed n r = ((n : ℝ) / (n + 1)) ^ n → r = 1 / (n + 1))) ∧
      wcFixed n (1 / (n + 1)) = ((n : ℝ) / (n + 1)) ^ n by
    have hmem : (1 : ℝ) / (n + 1) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    refine ⟨⟨⟨_, hmem, H.2⟩, ?_⟩, H.2, fun r hr h => (H.1 r hr).2 h⟩
    rintro y ⟨r, hr, rfl⟩
    exact (H.1 r hr).1
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    simp only [wcFixed, if_true, Nat.cast_one, pow_one]
    norm_num
    refine fun r _ _ => ⟨by rcases le_total r (1/2) with h | h <;> [left; right] <;> linarith,
      fun h => ?_⟩
    rcases lt_trichotomy r (1/2) with h' | h' | h'
    · have : 1 - r ≤ max (1 - r) r := le_max_left _ _
      linarith
    · exact h'
    · have : r ≤ max (1 - r) r := le_max_right _ _
      linarith
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have hk1 : k + 2 - 1 = k + 1 := by omega
    have hne : k + 2 ≠ 1 := by omega
    set N : ℝ := ((k + 2 : ℕ) : ℝ) with hNdef
    have hN : N = (k : ℝ) + 2 := by rw [hNdef]; push_cast; ring
    have hN2 : (2 : ℝ) ≤ N := by rw [hN]; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
    have hNpos : 0 < N := by linarith
    simp only [wcFixed, if_neg hne, hk1]
    have hr0half : 1 / (N + 1) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    constructor
    · intro r hr
      by_cases hrh : r ≤ 1 / 2
      · rw [if_pos hrh]
        have hD : 0 < (1 - r) * N - r := by nlinarith [hr.1]
        have h1r : 0 < 1 - r := by linarith
        set t : ℝ := ((1 - r) * N - r) / (N - 1) with ht
        have htpos : 0 < t := div_pos hD (by linarith)
        have hN1' : N - 1 ≠ 0 := by linarith
        have hDt : (1 - r) * N - r = (N - 1) * t := by rw [ht]; field_simp
        have hst : ((N - 1) * t + 1) / N = (N + 1) * (1 - r) / N := by
          rw [← hDt]; field_simp; ring
        obtain ⟨hle, hlt⟩ := amgm k N t hN htpos
        rw [hst] at hle hlt
        have hf : (1 - r) ^ (k + 2) * (N - 1) ^ (k + 1) / ((1 - r) * N - r) ^ (k + 1) =
            (1 - r) ^ (k + 2) / t ^ (k + 1) := by
          rw [hDt, mul_pow]
          have : (N - 1) ^ (k + 1) ≠ 0 := pow_ne_zero _ (by linarith)
          field_simp
        have hV : (N / (N + 1)) ^ (k + 2) = (1 - r) ^ (k + 2) / ((N + 1) * (1 - r) / N) ^ (k + 2) := by
          have : (1 - r) ^ (k + 2) ≠ 0 := by positivity
          rw [div_pow, div_pow, mul_pow]
          field_simp
        rw [hf, hV]
        have htp : 0 < t ^ (k + 1) := by positivity
        have hsp : 0 < ((N + 1) * (1 - r) / N) ^ (k + 2) := by positivity
        have h1rp : 0 < (1 - r) ^ (k + 2) := by positivity
        constructor
        · exact div_le_div_of_nonneg_left h1rp.le htp hle
        · intro heq
          by_contra hne'
          have ht1 : t ≠ 1 := by
            intro ht1
            apply hne'
            have : (1 - r) * N - r = N - 1 := by rw [hDt, ht1, mul_one]
            field_simp
            linarith
          have := div_lt_div_of_pos_left h1rp htp (hlt ht1)
          linarith
      · rw [if_neg hrh]
        have := V_le_half k N hN
        push_neg at hrh
        exact ⟨by linarith, fun h => by linarith⟩
    · rw [if_pos hr0half]
      have hN1 : N - 1 ≠ 0 := by linarith
      have e1 : 1 - 1 / (N + 1) = N / (N + 1) := by field_simp; ring
      have e2 : (1 - 1 / (N + 1)) * N - 1 / (N + 1) = N - 1 := by field_simp; ring
      rw [e2, e1]
      have : (N - 1) ^ (k + 1) ≠ 0 := pow_ne_zero _ hN1
      field_simp
      try rfl

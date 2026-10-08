-- Prove2me | solution 1 for QueueingFundamentals.AdvMarkov.retrial_mean_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:08:08.239307+00:00
-- url     : https://prove2.me/submissions/8b97f002-1e0e-431e-93d4-767769d065a7

import Mathlib
import Definitions.Def_QueueingFundamentals_AdvMarkov_Retrial

set_option autoImplicit false

namespace E8320a23

open QueueingFundamentals.AdvMarkov Filter

lemma cut (lam mu gam : ℝ) (p0 p1 : ℕ → ℝ) (h : RetrialBalance lam mu gam p0 p1) :
    ∀ n : ℕ, lam * p1 n = ((n : ℝ) + 1) * gam * p0 (n + 1) := by
  obtain ⟨h47, h48, h49⟩ := h
  intro n
  induction n with
  | zero =>
    have := h47 0
    simp at this ⊢
    linarith
  | succ k ih =>
    have h1 := h48 (k + 1) (by omega)
    have h2 := h47 (k + 1)
    simp only [Nat.add_sub_cancel] at h1
    push_cast at h1 h2 ⊢
    linarith

lemma rec' (lam mu gam : ℝ) (p0 p1 : ℕ → ℝ) (h : RetrialBalance lam mu gam p0 p1) (n : ℕ) :
    mu * gam * (((n : ℝ) + 1) * p0 (n + 1)) =
      lam * lam * p0 n + lam * gam * ((n : ℝ) * p0 n) := by
  have c := cut lam mu gam p0 p1 h n
  have e := h.1 n
  linear_combination (-mu) * c - lam * e

lemma summ2 (lam mu gam : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hgam : 0 < gam) (hlm : lam < mu)
    (p0 p1 : ℕ → ℝ) (hp0 : ∀ n, 0 ≤ p0 n) (h : RetrialBalance lam mu gam p0 p1) :
    Summable (fun n : ℕ => (n : ℝ) ^ 2 * p0 n) := by
  set K : ℝ := (4 * lam ^ 2 + 2 * lam * gam) / ((mu - lam) * gam) with hK
  have hd : 0 < (mu - lam) * gam := mul_pos (by linarith) hgam
  refine summable_of_ratio_norm_eventually_le (r := (1 + lam / mu) / 2) ?_ ?_
  · have : lam / mu < 1 := (div_lt_one hmu).2 hlm
    linarith
  · filter_upwards [eventually_ge_atTop (⌈K⌉₊ + 1)] with n hn
    have hnK : K ≤ (n : ℝ) := by
      have h1 : K ≤ (⌈K⌉₊ : ℝ) := Nat.le_ceil K
      have h2 : ((⌈K⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at h2
      linarith
    have hn1 : (1 : ℝ) ≤ n := by
      have : 1 ≤ n := by omega
      exact_mod_cast this
    have hA : 4 * lam ^ 2 + 2 * lam * gam ≤ (mu - lam) * gam * n := by
      have := mul_le_mul_of_nonneg_left hnK hd.le
      rwa [hK, mul_div_cancel₀ _ hd.ne'] at this
    have hpoly : ((n : ℝ) + 1) * (lam * (lam + n * gam)) ≤ (mu + lam) / 2 * gam * (n : ℝ) ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ n)
      have h2 : lam ^ 2 * 1 ≤ lam ^ 2 * n := mul_le_mul_of_nonneg_left hn1 (sq_nonneg lam)
      nlinarith [sq_nonneg lam, mul_pos hlam hgam]
    have hr := rec' lam mu gam p0 p1 h n
    have hp := hp0 n
    have hp' := hp0 (n + 1)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hp'),
      abs_of_nonneg (mul_nonneg (by positivity) hp)]
    push_cast
    have hmg : 0 < mu * gam := mul_pos hmu hgam
    refine le_of_mul_le_mul_left ?_ hmg
    calc mu * gam * (((n : ℝ) + 1) ^ 2 * p0 (n + 1))
        = (((n : ℝ) + 1) * (lam * (lam + n * gam))) * p0 n := by
          linear_combination ((n : ℝ) + 1) * hr
      _ ≤ ((mu + lam) / 2 * gam * (n : ℝ) ^ 2) * p0 n := mul_le_mul_of_nonneg_right hpoly hp
      _ = mu * gam * ((1 + lam / mu) / 2 * ((n : ℝ) ^ 2 * p0 n)) := by
          field_simp

end E8320a23

open QueueingFundamentals.AdvMarkov in
theorem solution (lam mu gam : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hgam : 0 < gam)
    (ρ : ℝ) (hρ : ρ = lam / mu) (hρ1 : ρ < 1)
    (p0 p1 : ℕ → ℝ) (hp : IsRetrialSteadyState lam mu gam p0 p1) :
    HasSum (fun n : ℕ => (n : ℝ) * (p0 n + p1 n)) (ρ ^ 2 / (1 - ρ) * ((mu + gam) / gam)) := by
  obtain ⟨hp0, hp1, hsum, hbal⟩ := hp
  have hlm : lam < mu := by rw [hρ, div_lt_one hmu] at hρ1; exact hρ1
  have h47 := hbal.1
  have hS2s := E8320a23.summ2 lam mu gam hlam hmu hgam hlm p0 p1 hp0 hbal
  have hS1s : Summable (fun n : ℕ => (n : ℝ) * p0 n) := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (Nat.cast_nonneg _) (hp0 n))
      (fun n => ?_) hS2s
    apply mul_le_mul_of_nonneg_right _ (hp0 n)
    have : n ≤ n ^ 2 := Nat.le_self_pow two_ne_zero n
    exact_mod_cast this
  have hP0s : Summable p0 :=
    Summable.of_nonneg_of_le hp0 (fun n => le_add_of_nonneg_right (hp1 n)) hsum.summable
  set P0 := ∑' n, p0 n with hP0def
  set S1 := ∑' n : ℕ, (n : ℝ) * p0 n with hS1def
  set S2 := ∑' n : ℕ, (n : ℝ) ^ 2 * p0 n with hS2def
  have hP0 : HasSum p0 P0 := hP0s.hasSum
  have hS1 : HasSum (fun n : ℕ => (n : ℝ) * p0 n) S1 := hS1s.hasSum
  have hS2 : HasSum (fun n : ℕ => (n : ℝ) ^ 2 * p0 n) S2 := hS2s.hasSum
  have hp1eq : ∀ n, p1 n = (lam * p0 n + gam * ((n : ℝ) * p0 n)) / mu := by
    intro n
    rw [eq_div_iff hmu.ne']
    linear_combination -(h47 n)
  -- E1
  have hsh1 : HasSum (fun n : ℕ => ((n : ℝ) + 1) * p0 (n + 1)) S1 := by
    have := (hasSum_nat_add_iff' 1).2 hS1
    simpa using this
  have E1 : mu * gam * S1 = lam * lam * P0 + lam * gam * S1 := by
    have h1 := hsh1.mul_left (mu * gam)
    have h2 := (hP0.mul_left (lam * lam)).add (hS1.mul_left (lam * gam))
    have hf : (fun n : ℕ => mu * gam * (((n : ℝ) + 1) * p0 (n + 1))) =
        fun n : ℕ => lam * lam * p0 n + lam * gam * ((n : ℝ) * p0 n) :=
      funext (E8320a23.rec' lam mu gam p0 p1 hbal)
    rw [hf] at h1
    exact h1.unique h2
  -- E2
  have hsh2 : HasSum (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * p0 (n + 1)) S2 := by
    have := (hasSum_nat_add_iff' 1).2 hS2
    simpa using this
  have E2 : mu * gam * S2 = lam * lam * P0 + lam * (lam + gam) * S1 + lam * gam * S2 := by
    have h1 := hsh2.mul_left (mu * gam)
    have h2 := ((hP0.mul_left (lam * lam)).add (hS1.mul_left (lam * (lam + gam)))).add
      (hS2.mul_left (lam * gam))
    have hf : (fun n : ℕ => mu * gam * (((n : ℝ) + 1) ^ 2 * p0 (n + 1))) =
        fun n : ℕ => lam * lam * p0 n + lam * (lam + gam) * ((n : ℝ) * p0 n) +
          lam * gam * ((n : ℝ) ^ 2 * p0 n) := by
      funext n
      have hr := E8320a23.rec' lam mu gam p0 p1 hbal n
      linear_combination ((n : ℝ) + 1) * hr
    rw [hf] at h1
    exact h1.unique h2
  -- E3
  have E3 : 1 = P0 + (lam * P0 + gam * S1) / mu := by
    have h2 := hP0.add (((hP0.mul_left lam).add (hS1.mul_left gam)).div_const mu)
    have hf : (fun n : ℕ => p0 n + p1 n) =
        fun n : ℕ => p0 n + (lam * p0 n + gam * ((n : ℝ) * p0 n)) / mu := by
      funext n
      rw [hp1eq n]
    rw [hf] at hsum
    exact hsum.unique h2
  have E3' : mu = mu * P0 + (lam * P0 + gam * S1) := by
    have : mu * 1 = mu * (P0 + (lam * P0 + gam * S1) / mu) := by rw [← E3]
    rw [mul_add, mul_div_cancel₀ _ hmu.ne', mul_one] at this
    exact this
  have hml : mu - lam ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlm)
  have hP : P0 * mu = mu - lam := by
    have : mu * (P0 * mu) = mu * (mu - lam) := by
      linear_combination (-(mu - lam)) * E3' + (-1) * E1
    exact mul_left_cancel₀ hmu.ne' this
  have hS1v : S1 * (mu * gam) = lam ^ 2 := by
    have : (mu - lam) * (S1 * (mu * gam)) = (mu - lam) * lam ^ 2 := by
      linear_combination mu * E1 + lam ^ 2 * hP
    exact mul_left_cancel₀ hml this
  have hS2v : S2 * (gam * (mu - lam)) = lam * lam * P0 + lam * (lam + gam) * S1 := by
    linear_combination E2
  have hP0e : P0 = (mu - lam) / mu := by rw [eq_div_iff hmu.ne']; exact hP
  have hS1e : S1 = lam ^ 2 / (mu * gam) := by
    rw [eq_div_iff (mul_pos hmu hgam).ne']; exact hS1v
  have hS2e : S2 = (lam * lam * P0 + lam * (lam + gam) * S1) / (gam * (mu - lam)) := by
    rw [eq_div_iff (mul_ne_zero hgam.ne' hml)]; exact hS2v
  have hval : S1 + (lam * S1 + gam * S2) / mu = ρ ^ 2 / (1 - ρ) * ((mu + gam) / gam) := by
    have h1r : 1 - lam / mu = (mu - lam) / mu := by field_simp
    rw [hS2e, hS1e, hP0e, hρ, h1r]
    field_simp
    ring
  have hfin : HasSum (fun n : ℕ => (n : ℝ) * (p0 n + p1 n)) (S1 + (lam * S1 + gam * S2) / mu) := by
    have h2 := hS1.add (((hS1.mul_left lam).add (hS2.mul_left gam)).div_const mu)
    have hf : (fun n : ℕ => (n : ℝ) * (p0 n + p1 n)) =
        fun n : ℕ => (n : ℝ) * p0 n + (lam * ((n : ℝ) * p0 n) + gam * ((n : ℝ) ^ 2 * p0 n)) / mu := by
      funext n
      rw [hp1eq n]
      ring
    rw [hf]
    exact h2
  rw [← hval]
  exact hfin

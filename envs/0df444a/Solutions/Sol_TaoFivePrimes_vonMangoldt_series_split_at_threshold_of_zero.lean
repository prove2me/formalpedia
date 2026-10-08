-- Prove2me | solution 1 for TaoFivePrimes.vonMangoldt_series_split_at_threshold_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:34:18.897716+00:00
-- url     : https://prove2.me/submissions/b2969a25-6a36-41ba-a267-a7ec91b4fcd7

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

set_option autoImplicit false

open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

namespace P460

lemma vm_eq (n : ℕ) : ((Λ n : ℝ) : ℂ) =
    ∑ d ∈ n.divisors, (-((((μ d : ℤ) : ℝ) : ℂ) * Real.log d)) := by
  have h := ArithmeticFunction.sum_moebius_mul_log_eq (n := n)
  simp only [ArithmeticFunction.log_apply] at h
  have h2 : ((Λ n : ℝ) : ℂ) = -((∑ d ∈ n.divisors, (μ d : ℝ) * Real.log d : ℝ) : ℂ) := by
    rw [h]; push_cast; ring
  rw [h2]; push_cast; rw [← Finset.sum_neg_distrib]

lemma inner_eq (f : ℕ → ℂ) (N : ℕ) (hN : ∀ n, N < n → f n = 0) (hf0 : f 0 = 0) (d : ℕ) :
    (∑' m : ℕ, f (d * m)) = ∑ m ∈ Finset.range (N+1), f (d * m) := by
  apply tsum_eq_sum
  intro m hm
  simp only [Finset.mem_range, not_lt] at hm
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simpa using hf0
  · apply hN; nlinarith

lemma inner_zero (f : ℕ → ℂ) (N : ℕ) (hN : ∀ n, N < n → f n = 0) (hf0 : f 0 = 0) (d : ℕ)
    (hd : N < d) : (∑' m : ℕ, f (d * m)) = 0 := by
  rw [inner_eq f N hN hf0 d]
  apply Finset.sum_eq_zero
  intro m _
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using hf0
  · apply hN; nlinarith

lemma outer_eq (f : ℕ → ℂ) (N : ℕ) (hN : ∀ n, N < n → f n = 0) (hf0 : f 0 = 0)
    (a : ℕ → ℂ) :
    (∑' d : ℕ, a d * (-((((μ d : ℤ) : ℝ) : ℂ) * Real.log d)) * (∑' m : ℕ, f (d * m))) =
      ∑ d ∈ Finset.range (N+1), a d * (-((((μ d : ℤ) : ℝ) : ℂ) * Real.log d)) *
        (∑ m ∈ Finset.range (N+1), f (d * m)) := by
  rw [tsum_eq_sum (s := Finset.range (N+1))]
  · apply Finset.sum_congr rfl
    intro d _
    rw [inner_eq f N hN hf0 d]
  · intro d hd
    simp only [Finset.mem_range, not_lt] at hd
    rw [inner_zero f N hN hf0 d (by omega), mul_zero]

lemma main (f : ℕ → ℂ) (N : ℕ) (hN : ∀ n, N < n → f n = 0) (hf0 : f 0 = 0) :
    (∑ n ∈ Finset.range (N+1), ((Λ n : ℝ) : ℂ) * f n) =
      ∑ d ∈ Finset.range (N+1), (-((((μ d : ℤ) : ℝ) : ℂ) * Real.log d)) *
        (∑ m ∈ Finset.range (N+1), f (d * m)) := by
  set c : ℕ → ℂ := fun d => (-((((μ d : ℤ) : ℝ) : ℂ) * Real.log d)) with hc
  have hR : (∑ d ∈ Finset.range (N+1), c d * (∑ m ∈ Finset.range (N+1), f (d * m))) =
      ∑ p ∈ Finset.range (N+1) ×ˢ Finset.range (N+1), c p.1 * f (p.1 * p.2) := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
  show _ = ∑ d ∈ Finset.range (N+1), c d * (∑ m ∈ Finset.range (N+1), f (d * m))
  rw [hR]
  rw [← Finset.sum_filter_of_ne (p := fun p : ℕ × ℕ => p.1 * p.2 ≤ N)]
  swap
  · intro x _ hx
    by_contra hcon
    exact hx (by rw [hN _ (by omega), mul_zero])
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.range (N+1)) (g := fun p : ℕ × ℕ => p.1 * p.2)]
  swap
  · intro x hx
    simp only [Finset.mem_filter] at hx
    simp only [Finset.mem_range]; omega
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Finset.mem_range] at hn
  rw [Finset.sum_congr rfl (g := fun x : ℕ × ℕ => c x.1 * f n)]
  swap
  · intro x hx
    simp only [Finset.mem_filter] at hx
    rw [hx.2]
  rw [← Finset.sum_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · simp [hf0]
  · have hset : (Finset.filter (fun x : ℕ × ℕ => x.1 * x.2 = n)
        (Finset.filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ N)
          (Finset.range (N+1) ×ˢ Finset.range (N+1)))) = n.divisorsAntidiagonal := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        Nat.mem_divisorsAntidiagonal]
      constructor
      · rintro ⟨⟨_, _⟩, h⟩
        exact ⟨h, by omega⟩
      · rintro ⟨h, _⟩
        have ha : a ≤ n := Nat.le_of_dvd hnpos ⟨b, h.symm⟩
        have hb : b ≤ n := Nat.le_of_dvd hnpos ⟨a, by rw [← h, mul_comm]⟩
        exact ⟨⟨⟨by omega, by omega⟩, by omega⟩, h⟩
    rw [hset, Nat.sum_divisorsAntidiagonal (fun a _ => c a), vm_eq]

end P460

open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius in
theorem solution (f : ℕ → ℂ) (U : ℕ)
    (hfin : Exists fun N0 : ℕ => forall n : ℕ, N0 < n -> f n = 0) (hf0 : f 0 = 0) :
    (∑' n : ℕ, ((Λ n : ℝ) : ℂ) * f n) =
      (∑' d : ℕ, (if d <= U then 1 else 0) * (-((((μ d : ℤ) : ℝ) : ℂ) * Real.log d)) *
        (∑' m : ℕ, f (d * m))) +
      (∑' d : ℕ, (if U < d then 1 else 0) * (-((((μ d : ℤ) : ℝ) : ℂ) * Real.log d)) *
        (∑' m : ℕ, f (d * m))) := by
  obtain ⟨N, hN⟩ := hfin
  rw [P460.outer_eq f N hN hf0, P460.outer_eq f N hN hf0, ← Finset.sum_add_distrib]
  rw [tsum_eq_sum (s := Finset.range (N+1))]
  · rw [P460.main f N hN hf0]
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> first | omega | ring
  · intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    rw [hN n (by omega), mul_zero]

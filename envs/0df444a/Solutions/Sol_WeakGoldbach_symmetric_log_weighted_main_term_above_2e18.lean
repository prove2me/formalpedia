-- Prove2me | solution 1 for WeakGoldbach.symmetric_log_weighted_main_term_above_2e18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @webmh
-- created : 2026-09-11T23:26:58.902341+00:00
-- url     : https://prove2.me/submissions/a8ef0106-7790-471f-8335-c2242c4f6900
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_symmetric_vonMangoldt_lower_bound_above_2e18
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

set_option autoImplicit false
open Finset
open ArithmeticFunction

private lemma sum_comp_le {s u : Finset ℕ} (f : ℕ → ℝ) (g : ℕ → ℕ)
    (hf : ∀ n, 0 ≤ f n) (hg : Set.InjOn g s)
    (hgu : ∀ n ∈ s, g n ∈ u) :
    ∑ n ∈ s, f (g n) ≤ ∑ n ∈ u, f n := by
  rw [← Finset.sum_image hg]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
    exact hgu a ha
  · intro n _ _
    exact hf n

private lemma prime_power_removal (m : ℕ) (hm : 2 ≤ m) :
    ∑ t ∈ range (m - 1), vonMangoldt (m - t) * vonMangoldt (m + t) ≤
    (∑ t ∈ (range (m - 1)).filter
      (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t)),
      Real.log (m - t : ℕ) * Real.log (m + t : ℕ)) +
    2 * Real.log (2 * m : ℕ) *
      (Chebyshev.psi (2 * m) - Chebyshev.theta (2 * m)) := by
  classical
  let f : ℕ → ℝ := fun n => if n.Prime then 0 else vonMangoldt n
  let L := Real.log (2 * m : ℕ)
  have hf : ∀ n, 0 ≤ f n := by intro n; dsimp [f]; split <;> positivity
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * m by omega))
  have hbound (n : ℕ) (hn : n ∈ Ioc 0 (2 * m)) : vonMangoldt n ≤ L := by
    have h := mem_Ioc.mp hn
    exact vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast h.1)
      (by exact_mod_cast h.2))
  have hleft (t : ℕ) (ht : t ∈ range (m - 1)) : m - t ∈ Ioc 0 (2 * m) := by
    simp only [mem_range] at ht
    simp only [mem_Ioc]; omega
  have hright (t : ℕ) (ht : t ∈ range (m - 1)) : m + t ∈ Ioc 0 (2 * m) := by
    simp only [mem_range] at ht
    simp only [mem_Ioc]; omega
  have hl := sum_comp_le f (fun t => m - t) hf
    (show Set.InjOn (fun t => m - t) (range (m - 1)) from by
      intro a ha b hb hab
      simp only [mem_coe, mem_range] at ha hb
      dsimp at hab
      omega) hleft
  have hr := sum_comp_le f (fun t => m + t) hf
    (show Set.InjOn (fun t => m + t) (range (m - 1)) from by
      intro a _ b _ hab; dsimp at hab; omega) hright
  have htotal : (∑ n ∈ Ioc 0 (2 * m), f n) =
      Chebyshev.psi (2 * m) - Chebyshev.theta (2 * m) := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
    have hcast : (2 : ℝ) * m = ((2 * m : ℕ) : ℝ) := by push_cast; rfl
    rw [hcast, Nat.floor_natCast]
    simp only [Finset.sum_filter]
    apply sum_congr rfl
    intro n _
    dsimp [f]
    split_ifs <;> simp_all
  have hpoint (t : ℕ) (ht : t ∈ range (m - 1)) :
      vonMangoldt (m - t) * vonMangoldt (m + t) ≤
      (if Nat.Prime (m - t) ∧ Nat.Prime (m + t) then
        Real.log (m - t : ℕ) * Real.log (m + t : ℕ) else 0) +
      L * (f (m - t) + f (m + t)) := by
    have ha := hbound _ (hleft t ht)
    have hb := hbound _ (hright t ht)
    have hna := vonMangoldt_nonneg (n := m - t)
    have hnb := vonMangoldt_nonneg (n := m + t)
    by_cases hp : Nat.Prime (m - t) <;> by_cases hq : Nat.Prime (m + t)
    · simp [hp, hq, f, vonMangoldt_apply_prime]
    · simp only [hp, hq, and_false, if_false, f, if_true, zero_add]
      exact mul_le_mul_of_nonneg_right ha hnb
    · simp only [hp, hq, false_and, if_false, f, if_true, add_zero, zero_add]
      nlinarith [mul_le_mul_of_nonneg_left hb hna]
    · simp only [hp, hq, false_and, if_false, f, zero_add]
      nlinarith [mul_le_mul_of_nonneg_right ha hnb, mul_nonneg hL hna]
  have hs := sum_le_sum hpoint
  simp only [sum_add_distrib, ← mul_sum, ← sum_filter] at hs
  rw [htotal] at hl hr
  change _ ≤ _ + 2 * L * _
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add hl hr) hL]

private lemma explicit_log_error (x : ℝ) (hx : (2048 : ℝ) ^ 4 ≤ x) :
    4 * Real.sqrt x * (Real.log x)^2 ≤ x / 8 := by
  have hx0 : 0 ≤ x := by positivity
  have hx1 : 1 ≤ x := by norm_num at hx ⊢; linarith
  let r := x ^ (1 / 8 : ℝ)
  have hr0 : 0 ≤ r := Real.rpow_nonneg hx0 _
  have hr8 : r ^ 8 = x := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  have hr4 : r ^ 4 = Real.sqrt x := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0, Real.sqrt_eq_rpow]
    norm_num
  have hr2 : 2048 ≤ r ^ 2 := by
    by_contra! h
    have hh : (r^2)^4 < (2048 : ℝ)^4 := by gcongr
    rw [← pow_mul] at hh
    norm_num at hh hx
    linarith
  have hlog : Real.log x ≤ 8 * r := by
    have hh := Real.log_le_rpow_div hx0 (show (0 : ℝ) < 1 / 8 by norm_num)
    dsimp [r]
    linarith
  have hlog0 := Real.log_nonneg hx1
  have hsquare : (Real.log x)^2 ≤ 64 * r^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsquare (show 0 ≤ 4 * r^4 by positivity)
  have hrest := mul_nonneg (sub_nonneg.mpr hr2) (show 0 ≤ r^6 by positivity)
  calc
    _ ≤ r^8 / 8 := by rw [← hr4]; nlinarith
    _ = x / 8 := by rw [hr8]

private lemma prime_power_error_small (m : ℕ) (hm : 2 * 10 ^ 18 < m) :
    2 * Real.log (2 * m : ℕ) *
      (Chebyshev.psi (2 * m) - Chebyshev.theta (2 * m)) ≤ (m : ℝ) / 4 := by
  have hmR : (2 * 10 ^ 18 : ℝ) < m := by exact_mod_cast hm
  have hx : (1 : ℝ) ≤ 2 * m := by linarith
  have hL := Real.log_nonneg hx
  have hcheb := Chebyshev.psi_sub_theta_le hx
  have hnum := explicit_log_error (2 * m) (by norm_num; linarith)
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hcheb (show 0 ≤ 2 * Real.log (2 * m) by positivity)]

/-- Conditional on the separately tracked von Mangoldt lower bound. -/
theorem solution (m : ℕ) (hm : 2 * 10 ^ 18 < m) :
    (∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2))
      * (m : ℝ) ≤
    ∑ t ∈ (Finset.range (m - 1)).filter
      (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t)),
      Real.log (m - t : ℕ) * Real.log (m + t : ℕ) := by
  have hS : (1 : ℝ) ≤
      ∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
    apply Finset.one_le_prod
    intro p hp
    have hpR : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
    apply (le_div_iff₀ (by linarith : (0 : ℝ) < p - 2)).2
    linarith
  have hmain := WeakGoldbach.symmetric_vonMangoldt_lower_bound_above_2e18 m hm
  have hremove := prime_power_removal m (by omega)
  have herror := prime_power_error_small m hm
  nlinarith [mul_le_mul_of_nonneg_right hS (show (0 : ℝ) ≤ m by positivity)]

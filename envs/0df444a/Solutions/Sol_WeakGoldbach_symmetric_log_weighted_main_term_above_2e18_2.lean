-- Prove2me | solution 2 for WeakGoldbach.symmetric_log_weighted_main_term_above_2e18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T04:13:49.447968+00:00
-- url     : https://prove2.me/submissions/d29f3a82-d9bc-4ddf-857b-87e88203c8b5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_weighted_symmetric_main_term_above_2e18
import Theorems.Thm_WeakGoldbach_prime_power_part_le_above_2e18
import Theorems.Thm_WeakGoldbach_singular_series_factor_ge_one

open Finset ArithmeticFunction

theorem _root_.solution (m : ℕ) (hm : 2 * 10 ^ 18 < m) :
    (∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2))
      * (m : ℝ) ≤
    ∑ t ∈ (Finset.range (m - 1)).filter
      (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t)),
      Real.log (m - t : ℕ) * Real.log (m + t : ℕ) := by
  set S : ℝ := ∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2) with hS
  set f : ℕ → ℝ := fun t => (ArithmeticFunction.vonMangoldt (m - t) : ℝ)
      * (ArithmeticFunction.vonMangoldt (m + t) : ℝ) with hfdef
  set F := (Finset.range (m - 1)).filter (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t)) with hF
  have hmR : (2 * 10 ^ 18 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hS1 : (1 : ℝ) ≤ S := WeakGoldbach.singular_series_factor_ge_one (2 * m)
  have hsplit : (∑ t ∈ F, f t)
      + ∑ t ∈ (Finset.range (m - 1)).filter
          (fun t => ¬ (Nat.Prime (m - t) ∧ Nat.Prime (m + t))), f t
      = ∑ t ∈ Finset.range (m - 1), f t :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hlow := WeakGoldbach.weighted_symmetric_main_term_above_2e18 m hm
  have hhigh := WeakGoldbach.prime_power_part_le_above_2e18 m hm
  have hFlow : S * (m : ℝ) * (23 / 20) ≤ ∑ t ∈ F, f t := by
    simp only [hS, hfdef] at hlow hhigh ⊢
    linarith [hsplit]
  -- on the prime pairs the von Mangoldt weights are logarithms
  have hlogs : (∑ t ∈ F, f t)
      = ∑ t ∈ F, Real.log (m - t : ℕ) * Real.log (m + t : ℕ) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have h := (Finset.mem_filter.1 ht).2
    simp only [hfdef]
    rw [ArithmeticFunction.vonMangoldt_apply_prime h.1,
      ArithmeticFunction.vonMangoldt_apply_prime h.2]
  rw [← hlogs]
  have final : ∀ S' mm T : ℝ, 1 ≤ S' → 0 < mm → S' * mm * (23 / 20) ≤ T → S' * mm ≤ T := by
    intro S' mm T hS' hmm h
    nlinarith
  exact final S (m : ℝ) _ hS1 (by linarith) hFlow

#print axioms solution

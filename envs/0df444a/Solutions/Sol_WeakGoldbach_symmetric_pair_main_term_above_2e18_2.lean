-- Prove2me | solution 2 for WeakGoldbach.symmetric_pair_main_term_above_2e18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T02:50:56.031841+00:00
-- url     : https://prove2.me/submissions/a288379d-962a-459b-b596-28ec182d686c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_weighted_symmetric_main_term_above_2e18
import Theorems.Thm_WeakGoldbach_prime_power_part_le_above_2e18

/-!
`symmetric_pair_main_term_above_2e18` from the weighted lower bound and the
prime-power upper bound.
-/

open Finset ArithmeticFunction

theorem _root_.solution (m : ℕ) (hm : 2 * 10 ^ 18 < m) :
    (∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2))
      * (m : ℝ) / (Real.log m) ^ 2
      ≤ ((Finset.range (m - 1)).filter
        (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t))).card := by
  set S : ℝ := ∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2) with hS
  set f : ℕ → ℝ := fun t => (ArithmeticFunction.vonMangoldt (m - t) : ℝ)
      * (ArithmeticFunction.vonMangoldt (m + t) : ℝ) with hfdef
  set F := (Finset.range (m - 1)).filter (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t)) with hF
  have hmR : (2 * 10 ^ 18 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm1 : (1 : ℝ) < (m : ℝ) := by linarith
  have hL : 0 < Real.log m := Real.log_pos hm1
  -- `20 log 2 ≤ 3 log m`, i.e. `2 ^ 20 ≤ m ^ 3`
  have hcube : (2 : ℝ) ^ 20 ≤ (m : ℝ) ^ 3 := by
    have h1 : (1048576 : ℝ) ≤ (m : ℝ) := by linarith
    calc (2 : ℝ) ^ 20 = 1048576 := by norm_num
      _ ≤ (m : ℝ) := h1
      _ = (m : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (m : ℝ) ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h20 : 20 * Real.log 2 ≤ 3 * Real.log m := by
    have e1 : Real.log ((2 : ℝ) ^ 20) = 20 * Real.log 2 := by
      rw [Real.log_pow]; norm_num
    have e2 : Real.log ((m : ℝ) ^ 3) = 3 * Real.log m := by
      rw [Real.log_pow]; norm_num
    calc 20 * Real.log 2 = Real.log ((2 : ℝ) ^ 20) := e1.symm
      _ ≤ Real.log ((m : ℝ) ^ 3) := Real.log_le_log (by positivity) hcube
      _ = 3 * Real.log m := e2
  have hlog2m : Real.log (2 * (m : ℝ)) = Real.log 2 + Real.log m :=
    Real.log_mul two_ne_zero (by positivity)
  -- split the full sum
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
  -- upper bound on each surviving term
  have hsummand : ∀ t ∈ F, f t ≤ Real.log m * Real.log (2 * (m : ℝ)) := by
    intro t ht
    have ht' : t < m - 1 := Finset.mem_range.1 (Finset.mem_filter.1 ht).1
    have hmt : 2 ≤ m - t := by omega
    have hp1 : (1 : ℝ) ≤ ((m - t : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_of_lt hmt
    have hp1' : (0 : ℝ) < ((m - t : ℕ) : ℝ) := by linarith
    have hle1 : ((m - t : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.sub_le m t
    have hp2 : (1 : ℝ) ≤ ((m + t : ℕ) : ℝ) := by
      have : 1 ≤ m + t := by omega
      exact_mod_cast this
    have hp2' : (0 : ℝ) < ((m + t : ℕ) : ℝ) := by linarith
    have hle2 : ((m + t : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by
      have : m + t ≤ 2 * m := by omega
      calc ((m + t : ℕ) : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast this
        _ = 2 * (m : ℝ) := by push_cast; ring
    have hlg1 : (0 : ℝ) ≤ Real.log ((m - t : ℕ) : ℝ) := Real.log_nonneg hp1
    calc f t ≤ Real.log ((m - t : ℕ) : ℝ) * Real.log ((m + t : ℕ) : ℝ) :=
          mul_le_mul ArithmeticFunction.vonMangoldt_le_log
            ArithmeticFunction.vonMangoldt_le_log
            ArithmeticFunction.vonMangoldt_nonneg hlg1
      _ ≤ Real.log m * Real.log (2 * (m : ℝ)) :=
          mul_le_mul (Real.log_le_log hp1' hle1) (Real.log_le_log hp2' hle2)
            (Real.log_nonneg hp2) (Real.log_nonneg (by linarith))
  have hub : (∑ t ∈ F, f t) ≤ (F.card : ℝ) * (Real.log m * Real.log (2 * (m : ℝ))) := by
    calc (∑ t ∈ F, f t) ≤ ∑ _t ∈ F, Real.log m * Real.log (2 * (m : ℝ)) :=
          Finset.sum_le_sum hsummand
      _ = (F.card : ℝ) * (Real.log m * Real.log (2 * (m : ℝ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (0 : ℝ) ≤ (F.card : ℝ) := Nat.cast_nonneg _
  have hstep1 : Real.log m * Real.log (2 * (m : ℝ)) ≤ (23 / 20) * Real.log m ^ 2 := by
    rw [hlog2m]
    nlinarith [mul_le_mul_of_nonneg_left h20 hL.le, hL]
  have hstep2 : (F.card : ℝ) * (Real.log m * Real.log (2 * (m : ℝ)))
      ≤ (F.card : ℝ) * ((23 / 20) * Real.log m ^ 2) :=
    mul_le_mul_of_nonneg_left hstep1 hcard
  rw [div_le_iff₀ (by positivity)]
  linarith [hFlow, hub, hstep2]

#print axioms solution

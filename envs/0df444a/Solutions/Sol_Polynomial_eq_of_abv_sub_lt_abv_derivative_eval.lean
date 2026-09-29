-- Prove2me | solution 1 for Polynomial.eq_of_abv_sub_lt_abv_derivative_eval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/3e680d3f-6d74-5ebd-8487-20b902b1d98a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_eq_of_abv_sub_lt_abv_derivative_eval

set_option autoImplicit false

open Polynomial

namespace P2MRootSep

variable {K : Type*} [Field K] (μ : AbsoluteValue K ℝ)

theorem abv_sum_le (hμ : IsNonarchimedean μ) {ι : Type*} (s : Finset ι) (f : ι → K) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i ∈ s, μ (f i) ≤ C) : μ (∑ i ∈ s, f i) ≤ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hC
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hμ _ _).trans (max_le (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem abv_natCast_le_one (hμ : IsNonarchimedean μ) : ∀ n : ℕ, μ (n : K) ≤ 1
  | 0 => by simp
  | n + 1 => by
    rw [Nat.cast_succ]
    exact (hμ _ _).trans (max_le (abv_natCast_le_one hμ n) (by rw [map_one]))

theorem abv_taylor_coeff_le_one (hμ : IsNonarchimedean μ) (g : Polynomial K) (hg : ∀ i, μ (g.coeff i) ≤ 1)
    (a : K) (ha : μ a ≤ 1) (n : ℕ) : μ ((taylor a g).coeff n) ≤ 1 := by
  rw [taylor_coeff, eval_eq_sum_range]
  refine abv_sum_le μ hμ _ _ zero_le_one fun i _ => ?_
  rw [hasseDeriv_coeff, map_mul, map_mul, map_pow]
  exact mul_le_one₀ (mul_le_one₀ (abv_natCast_le_one μ hμ _) (apply_nonneg _ _) (hg _))
    (pow_nonneg (apply_nonneg _ _) _) (pow_le_one₀ (apply_nonneg _ _) ha)

end P2MRootSep

open Polynomial in

theorem solution
    {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ)
    (g : Polynomial K) (hg : ∀ i, μ (g.coeff i) ≤ 1) {a b : K} (ha : μ a ≤ 1) (hb : μ b ≤ 1)
    (hga : g.eval a = 0) (hgb : g.eval b = 0)
    (hlt : μ (a - b) < μ ((Polynomial.derivative g).eval a)) : a = b := by
  by_contra hab
  set d : K := b - a with hd
  have hd0 : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hdle : μ d ≤ 1 := by
    rw [hd, sub_eq_add_neg]
    exact (hμ _ _).trans (max_le hb (by rw [μ.map_neg]; exact ha))
  have hdd : μ d = μ (a - b) := by rw [hd, ← neg_sub, μ.map_neg]
  have hdlt : μ d < μ ((derivative g).eval a) := by rw [hdd]; exact hlt

  set T := taylor a g with hT
  have hc : ∀ n, μ (T.coeff n) ≤ 1 := P2MRootSep.abv_taylor_coeff_le_one μ hμ g hg a ha
  have hev : T.eval d = 0 := by rw [hT, taylor_eval, hd, sub_add_cancel, hgb]
  have hexp := eval_eq_sum_range' (p := T) (n := T.natDegree + 3) (x := d) (by omega)
  rw [Finset.sum_range_succ', Finset.sum_range_succ'] at hexp
  have h0 : T.coeff 0 = 0 := by rw [hT, taylor_coeff_zero, hga]
  have h1 : T.coeff 1 = (derivative g).eval a := by rw [hT, taylor_coeff_one]
  rw [hev, h0, h1, pow_zero, zero_mul, add_zero, pow_one] at hexp

  set S : K := ∑ i ∈ Finset.range (T.natDegree + 1), T.coeff (i + 1 + 1) * d ^ i with hS
  have hSle : μ S ≤ 1 := by
    refine P2MRootSep.abv_sum_le μ hμ _ _ zero_le_one fun i _ => ?_
    rw [map_mul, map_pow]
    exact mul_le_one₀ (hc _) (pow_nonneg (apply_nonneg _ _) _) (pow_le_one₀ (apply_nonneg _ _) hdle)
  have hsum : ∑ i ∈ Finset.range (T.natDegree + 1), T.coeff (i + 1 + 1) * d ^ (i + 1 + 1) = d ^ 2 * S := by
    rw [hS, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum] at hexp

  have hkey : (derivative g).eval a = -(d * S) := by
    have : d * ((derivative g).eval a + d * S) = 0 := by linear_combination -hexp
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hd0
    · linear_combination h
  have : μ ((derivative g).eval a) ≤ μ d := by
    rw [hkey, μ.map_neg, map_mul]
    exact mul_le_of_le_one_right (apply_nonneg μ d) hSle
  exact absurd hdlt (not_lt.mpr this)

end S_Polynomial_eq_of_abv_sub_lt_abv_derivative_eval
end P2MW
export P2MW.S_Polynomial_eq_of_abv_sub_lt_abv_derivative_eval (solution)

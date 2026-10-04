-- Prove2me | solution 1 for ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient_eq_even
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-03T15:53:01.175511+00:00
-- url     : https://prove2.me/submissions/c3fb8d5f-9a84-4738-83bd-33061b837c1b

import Definitions.Def_ZetaNine_CoefficientMap
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

/-!
Finite entry to route Z9.F, specialized to p = 9, q = 1, m = n.
The rational expression is defined by its actual numerator and pole product.
The cleared expression agrees with (t+j)^9 R_n(t) at every regular point,
has nonzero denominator at -j, and its value there is computed from the
products. No coefficient closed formula is used as its definition.

This file does not establish lower partial fractions, the full formal map,
invertibility, the exact infinite sum, or irrationality.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators
open Finset
open Polynomial

namespace ZetaNine.CoefficientMap



















theorem poleProduct_factor (n j : ℕ) (hj : j ≤ n) (t : ℚ) :
    poleProduct n t = (t + j) * clearedPoleProduct n j t := by
  exact (Finset.mul_prod_erase (range (n + 1)) (fun k => t + (k : ℚ))
    (by simpa using Nat.lt_succ_iff.mpr hj)).symm

theorem poleProduct_ne_zero (n : ℕ) (t : ℚ)
    (ht : ∀ k ≤ n, t + (k : ℚ) ≠ 0) : poleProduct n t ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact ht k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

theorem clearedPoleProduct_ne_zero (n j : ℕ) :
    clearedPoleProduct n j (-(j : ℚ)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  have hkj := (Finset.mem_erase.mp hk).1
  intro hz
  have he : (k : ℚ) = (j : ℚ) := by linarith
  exact hkj (Nat.cast_inj.mp he)

theorem clear_highest_pole (n j : ℕ) (hj : j ≤ n) (t : ℚ)
    (ht : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    actualR n t * (t + j) ^ 9 = clearedR n j t := by
  have hfactor := ht j hj
  have hclear : clearedPoleProduct n j t ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact ht k (Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_erase.mp hk).2))
  unfold actualR clearedR
  rw [poleProduct_factor n j hj t, mul_pow]
  field_simp

theorem clear_weighted_highest_pole (n j : ℕ) (hj : j ≤ n)
    (W : ℚ[X]) (t : ℚ) (ht : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    weightedR n W t * (t + j) ^ 9 = clearedWeightedR n j W t := by
  unfold weightedR clearedWeightedR
  rw [mul_right_comm, clear_highest_pole n j hj t ht]

theorem rising_product (a n : ℕ) :
    (∏ i ∈ range n, ((a : ℚ) + ((i : ℚ) + 1))) =
      (n.factorial : ℚ) * ((a + n).choose n : ℚ) := by
  have h := Nat.ascFactorial_eq_factorial_mul_choose a n
  rw [Nat.ascFactorial_eq_prod_range] at h
  have hc := congrArg (fun x : ℕ => (x : ℚ)) h
  simp only [Nat.cast_prod, Nat.cast_add, Nat.cast_mul, Nat.cast_one] at hc
  calc
    _ = ∏ i ∈ range n, ((a : ℚ) + 1 + i) := by
      apply Finset.prod_congr rfl
      intro i hi
      ring
    _ = _ := hc

theorem falling_product (n : ℕ) :
    (∏ k ∈ range n, ((k : ℚ) - n)) =
      (-1 : ℚ) ^ n * (n.factorial : ℚ) := by
  calc
    (∏ k ∈ range n, ((k : ℚ) - n)) =
        ∏ k ∈ range n, (-((n : ℚ) - k)) := by
      apply Finset.prod_congr rfl
      intro k hk
      ring
    _ = (-1 : ℚ) ^ n * (∏ k ∈ range n, ((n : ℚ) - k)) := by
      rw [Finset.prod_neg, Finset.card_range]
    _ = (-1 : ℚ) ^ n * (n.factorial : ℚ) := by
      rw [Finset.prod_range_natCast_sub, ← Nat.descFactorial_eq_prod_range,
        Nat.descFactorial_self]

theorem clearedPoleProduct_eval (n j : ℕ) (hj : j ≤ n) :
    clearedPoleProduct n j (-(j : ℚ)) =
      (-1 : ℚ) ^ j * (j.factorial : ℚ) * ((n - j).factorial : ℚ) := by
  induction n with
  | zero =>
    have : j = 0 := by omega
    subst j
    simp [clearedPoleProduct]
  | succ n ih =>
    by_cases hlast : j = n + 1
    · subst j
      rw [clearedPoleProduct, Finset.range_add_one, Finset.erase_insert (by simp)]
      have hprod := falling_product (n + 1)
      simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one]
      convert hprod using 1
      apply Finset.prod_congr rfl
      intro k hk
      ring
    · have hjn : j ≤ n := by omega
      have hnmem : n + 1 ∉ (range (n + 1)).erase j := by simp
      unfold clearedPoleProduct
      rw [Finset.range_add_one, Finset.erase_insert_of_ne (Ne.symm hlast), Finset.prod_insert hnmem]
      change (-(j : ℚ) + (n + 1 : ℕ)) * clearedPoleProduct n j (-(j : ℚ)) = _
      rw [ih hjn]
      have hsub : n + 1 - j = (n - j) + 1 := by omega
      rw [hsub, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hcast : ((n - j : ℕ) : ℚ) = (n : ℚ) - j := Nat.cast_sub hjn
      simp only [Nat.cast_add, Nat.cast_one, hcast]
      ring

theorem numerator_eval (n j : ℕ) (hj : j ≤ n) :
    numerator n (-(j : ℚ)) =
      (-1 : ℚ) ^ n * (n.factorial : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) := by
  have hleft : (∏ i ∈ range n, (-(j : ℚ) - ((i : ℚ) + 1))) =
      (-1 : ℚ) ^ n * (n.factorial : ℚ) * ((n + j).choose n : ℚ) := by
    calc
      _ = ∏ i ∈ range n, (-((j : ℚ) + ((i : ℚ) + 1))) := by
        apply Finset.prod_congr rfl
        intro i hi
        ring
      _ = (-1 : ℚ) ^ n * (n.factorial : ℚ) * ((n + j).choose n : ℚ) := by
        rw [Finset.prod_neg, Finset.card_range, rising_product, Nat.add_comm j n]
        ring
  have hright : (∏ i ∈ range n, (-(j : ℚ) + n + ((i : ℚ) + 1))) =
      (n.factorial : ℚ) * ((2 * n - j).choose n : ℚ) := by
    have hsum : n - j + n = 2 * n - j := by omega
    rw [← hsum, ← rising_product (n - j) n]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Nat.cast_sub hj]
    ring
  unfold numerator
  rw [hleft, hright]
  ring

theorem leadingPoleCoefficient_eq (n j : ℕ) (hj : j ≤ n) :
    leadingPoleCoefficient n j =
      (-1 : ℚ) ^ (n + j) * (n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) := by
  unfold leadingPoleCoefficient clearedR
  rw [numerator_eval n j hj, clearedPoleProduct_eval n j hj, Nat.cast_choose ℚ hj,
    pow_add]
  have hjfac : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have hdfac : ((n - j).factorial : ℚ) ≠ 0 := by exact_mod_cast (n - j).factorial_ne_zero
  rcases Nat.even_or_odd j with h | h
  · rw [h.neg_one_pow]
    field_simp
  · rw [h.neg_one_pow]
    field_simp

theorem leadingPoleCoefficient_eq_even (n j : ℕ) (hn : Even n) (hj : j ≤ n) :
    leadingPoleCoefficient n j =
      (-1 : ℚ) ^ j * (n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) := by
  rw [leadingPoleCoefficient_eq n j hj, pow_add, hn.neg_one_pow, one_mul]

theorem leadingPoleCoefficient_ne_zero (n j : ℕ) (hj : j ≤ n) :
    leadingPoleCoefficient n j ≠ 0 := by
  rw [leadingPoleCoefficient_eq n j hj]
  have h1 : 0 < n.choose j := Nat.choose_pos hj
  have h2 : 0 < (n + j).choose n := Nat.choose_pos (by omega)
  have h3 : 0 < (2 * n - j).choose n := Nat.choose_pos (by omega)
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by exact_mod_cast h1.ne'))
    · exact_mod_cast h2.ne'
  · exact_mod_cast h3.ne'

theorem leadingPoleCoefficient_is_integer (n j : ℕ) (hj : j ≤ n) :
    ∃ z : ℤ, leadingPoleCoefficient n j = (z : ℚ) := by
  refine ⟨(-1 : ℤ) ^ (n + j) * (n.choose j : ℤ) ^ 9 *
    ((n + j).choose n : ℤ) * ((2 * n - j).choose n : ℤ), ?_⟩
  rw [leadingPoleCoefficient_eq n j hj]
  push_cast
  rfl

theorem signed_leadingPoleCoefficient_pos_even (n j : ℕ) (hn : Even n) (hj : j ≤ n) :
    (-1 : ℚ) ^ j * leadingPoleCoefficient n j > 0 := by
  have hs : ((-1 : ℚ) ^ j) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
    norm_num
  have h1 : 0 < n.choose j := Nat.choose_pos hj
  have h2 : 0 < (n + j).choose n := Nat.choose_pos (by omega)
  have h3 : 0 < (2 * n - j).choose n := Nat.choose_pos (by omega)
  rw [leadingPoleCoefficient_eq_even n j hn hj]
  have he : (-1 : ℚ) ^ j * ((-1 : ℚ) ^ j * (n.choose j : ℚ) ^ 9 *
      ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ)) =
      ((-1 : ℚ) ^ j) ^ 2 * ((n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ)) := by ring
  rw [he, hs, one_mul]
  positivity

theorem local_coordinate_identity (n j : ℕ) (hj : j ≤ n) (z : ℚ) :
    (-(j : ℚ) + z) * (-(j : ℚ) + z + n) =
      -(j : ℚ) * (n - j : ℕ) + ((n : ℚ) - 2 * j) * z + z ^ 2 := by
  rw [Nat.cast_sub hj]
  ring

theorem clearedWeightedR_local_coordinate (n j : ℕ) (hj : j ≤ n)
    (W : ℚ[X]) (z : ℚ) :
    clearedWeightedR n j W (-(j : ℚ) + z) =
      clearedR n j (-(j : ℚ) + z) *
        W.eval (-(j : ℚ) * (n - j : ℕ) + ((n : ℚ) - 2 * j) * z + z ^ 2) := by
  unfold clearedWeightedR
  rw [local_coordinate_identity n j hj z]

theorem weightedLeadingPoleCoefficient_eq (n j : ℕ) (hj : j ≤ n) (W : ℚ[X]) :
    weightedLeadingPoleCoefficient n j W =
      (-1 : ℚ) ^ (n + j) * (n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) *
          W.eval (-(j : ℚ) * (n - j : ℕ)) := by
  unfold weightedLeadingPoleCoefficient clearedWeightedR
  change leadingPoleCoefficient n j * W.eval (-(j : ℚ) * (-(j : ℚ) + n)) = _
  rw [leadingPoleCoefficient_eq n j hj, Nat.cast_sub hj]
  congr 2
  ring

theorem checked_weightedLeadingPoleCoefficient_eq_even (n j : ℕ) (hn : Even n)
    (hj : j ≤ n) (W : ℚ[X]) :
    weightedLeadingPoleCoefficient n j W =
      (-1 : ℚ) ^ j * (n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) *
          W.eval (-(j : ℚ) * (n - j : ℕ)) := by
  rw [weightedLeadingPoleCoefficient_eq n j hj W, pow_add, hn.neg_one_pow, one_mul]

end ZetaNine.CoefficientMap











open ZetaNine.CoefficientMap

theorem solution (n j : ℕ) (hn : Even n)
    (hj : j ≤ n) (W : ℚ[X]) :
    weightedLeadingPoleCoefficient n j W =
      (-1 : ℚ) ^ j * (n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) *
          W.eval (-(j : ℚ) * (n - j : ℕ)) := by
  exact ZetaNine.CoefficientMap.checked_weightedLeadingPoleCoefficient_eq_even n j hn hj W

#print axioms solution

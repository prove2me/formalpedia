-- Prove2me | solution 1 for ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-08T14:56:03.713089+00:00
-- url     : https://prove2.me/submissions/3c9c8466-3e7c-419a-bd9c-83989ed8dd35

import Definitions.Def_ZetaNine_AnalyticUniformWeighted
import Mathlib

/- SOURCE module: CoefficientMap; complete theorem bodies retained. -/

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

theorem weightedLeadingPoleCoefficient_eq_even (n j : ℕ) (hn : Even n)
    (hj : j ≤ n) (W : ℚ[X]) :
    weightedLeadingPoleCoefficient n j W =
      (-1 : ℚ) ^ j * (n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) *
          W.eval (-(j : ℚ) * (n - j : ℕ)) := by
  rw [weightedLeadingPoleCoefficient_eq n j hj W, pow_add, hn.neg_one_pow, one_mul]

end ZetaNine.CoefficientMap

#print axioms ZetaNine.CoefficientMap.clear_highest_pole
#print axioms ZetaNine.CoefficientMap.clearedPoleProduct_ne_zero
#print axioms ZetaNine.CoefficientMap.leadingPoleCoefficient_eq
#print axioms ZetaNine.CoefficientMap.leadingPoleCoefficient_ne_zero
#print axioms ZetaNine.CoefficientMap.leadingPoleCoefficient_is_integer
#print axioms ZetaNine.CoefficientMap.signed_leadingPoleCoefficient_pos_even
#print axioms ZetaNine.CoefficientMap.clearedWeightedR_local_coordinate
#print axioms ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient_eq_even


/- SOURCE module: AnalyticFactorialBounds; complete theorem bodies retained. -/

/-!
SOURCE preparation: elementary factorial logarithm bounds for the actual
ZetaNine rational function. This file has not been compiled or kernel checked.
Every endpoint has a complete proof body; no estimate is an input hypothesis.

The lower bound also holds at zero because Real.log 0 = 0. The upper bound is
stated only for n >= 1. Both induction steps use log x <= x - 1, applied to
the two reciprocal ratios n/(n+1) and (n+1)/n.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZetaNine.AnalyticFactorialBounds

theorem real_factorial_pos (n : ℕ) : 0 < (n.factorial : ℝ) := by
  exact_mod_cast Nat.factorial_pos n

theorem log_factorial_succ (n : ℕ) :
    Real.log ((n + 1).factorial : ℝ) =
      Real.log ((n : ℝ) + 1) + Real.log (n.factorial : ℝ) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  exact Real.log_mul (by positivity) (real_factorial_pos n).ne'

/-- The induction increment for the lower factorial bound. -/
theorem log_successor_increment_upper (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) ≤ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hn1 hn0)
  rw [Real.log_div hn1.ne' hn0.ne'] at h
  calc
    (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) ≤
        (n : ℝ) * (((n : ℝ) + 1) / (n : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left h hn0.le
    _ = 1 := by field_simp [hn0.ne']; ring

/-- The induction increment for the upper factorial bound. -/
theorem log_successor_increment_lower (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ ((n : ℝ) + 1) *
      (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hn0 hn1)
  rw [Real.log_div hn0.ne' hn1.ne'] at h
  have hmul := mul_le_mul_of_nonneg_left h hn1.le
  have he : ((n : ℝ) + 1) * ((n : ℝ) / ((n : ℝ) + 1) - 1) = -1 := by
    field_simp [hn1.ne']
    ring
  rw [he] at hmul
  nlinarith

/-- Genuine lower bound, including n = 0. -/
theorem log_factorial_lower (n : ℕ) :
    (n : ℝ) * Real.log (n : ℝ) - n ≤ Real.log (n.factorial : ℝ) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      norm_num
    · have hn1 : 1 ≤ n := by omega
      have hstep := log_successor_increment_upper n hn1
      rw [log_factorial_succ, Nat.cast_add, Nat.cast_one]
      nlinarith

/-- Genuine upper bound, with the positive-index domain used below. -/
theorem log_factorial_upper (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤
      ((n : ℝ) + 1) * Real.log (n : ℝ) - n + 1 := by
  have hall : ∀ m : ℕ, 1 ≤ m →
      Real.log (m.factorial : ℝ) ≤
        ((m : ℝ) + 1) * Real.log (m : ℝ) - m + 1 := by
    intro m
    induction m with
    | zero => intro hm; omega
    | succ m ih =>
      intro hm
      by_cases hm0 : m = 0
      · subst m
        norm_num
      · have hm1 : 1 ≤ m := by omega
        have hprevious := ih hm1
        have hstep := log_successor_increment_lower m hm1
        rw [log_factorial_succ, Nat.cast_add, Nat.cast_one]
        nlinarith
  exact hall n hn

/-- Remove the shifted factorial exactly before estimating the logarithm. -/
theorem log_factorial_pred (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n - 1).factorial : ℝ) =
      Real.log (n.factorial : ℝ) - Real.log (n : ℝ) := by
  have hnrec : n - 1 + 1 = n := by omega
  have h := log_factorial_succ (n - 1)
  rw [hnrec] at h
  have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast hnrec
  rw [hcast] at h
  linarith

end ZetaNine.AnalyticFactorialBounds

#print axioms ZetaNine.AnalyticFactorialBounds.real_factorial_pos
#print axioms ZetaNine.AnalyticFactorialBounds.log_factorial_succ
#print axioms ZetaNine.AnalyticFactorialBounds.log_successor_increment_upper
#print axioms ZetaNine.AnalyticFactorialBounds.log_successor_increment_lower
#print axioms ZetaNine.AnalyticFactorialBounds.log_factorial_lower
#print axioms ZetaNine.AnalyticFactorialBounds.log_factorial_upper
#print axioms ZetaNine.AnalyticFactorialBounds.log_factorial_pred


/- SOURCE module: AnalyticRationalFactorial; complete theorem bodies retained. -/

/-!
UNCOMPILED SOURCE preparation. These endpoints start from the actual
CoefficientMap.numerator/poleProduct products. The factorial formula is a
conclusion, never a hypothesis. No logarithmic bound or moment estimate is
claimed to have passed Lean or kernel verification.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section
open scoped BigOperators
open Finset

namespace ZetaNine.AnalyticRationalFactorial

theorem rational_factorial_ne_zero (n : ℕ) : (n.factorial : ℚ) ≠ 0 := by
  exact_mod_cast Nat.factorial_ne_zero n

theorem ascending_product_factorial (a m : ℕ) (ha : 1 ≤ a) :
    (∏ i ∈ range m, ((a : ℚ) + (i : ℚ))) =
      ((a + m - 1).factorial : ℚ) / ((a - 1).factorial : ℚ) := by
  have h := Nat.factorial_mul_ascFactorial' a m (by omega : 0 < a)
  rw [Nat.ascFactorial_eq_prod_range] at h
  have hc := congrArg (fun z : ℕ => (z : ℚ)) h
  simp only [Nat.cast_mul, Nat.cast_prod, Nat.cast_add] at hc
  apply (eq_div_iff (rational_factorial_ne_zero (a - 1))).mpr
  simpa only [mul_comm] using hc

theorem actual_falling_product_factorial (n k : ℕ) (hk : n < k) :
    (∏ i ∈ range n, ((k : ℚ) - ((i : ℚ) + 1))) =
      ((k - 1).factorial : ℚ) / ((k - n - 1).factorial : ℚ) := by
  have hk1 : 1 ≤ k := by omega
  have hpred : ((k - 1 : ℕ) : ℚ) = (k : ℚ) - 1 := by
    exact_mod_cast (Nat.cast_sub hk1 : ((k - 1 : ℕ) : ℚ) = (k : ℚ) - 1)
  have hproduct :
      (∏ i ∈ range n, ((k : ℚ) - ((i : ℚ) + 1))) =
        ((k - 1).descFactorial n : ℚ) := by
    calc
      _ = ∏ i ∈ range n, (((k - 1 : ℕ) : ℚ) - (i : ℚ)) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [hpred]
        ring
      _ = _ := by
        rw [Finset.prod_range_natCast_sub, ← Nat.descFactorial_eq_prod_range]
  rw [hproduct]
  have h := Nat.factorial_mul_descFactorial (by omega : n ≤ k - 1)
  have hc := congrArg (fun z : ℕ => (z : ℚ)) h
  have hindex : k - 1 - n = k - n - 1 := by omega
  simp only [Nat.cast_mul, hindex] at hc
  apply (eq_div_iff (rational_factorial_ne_zero (k - n - 1))).mpr
  simpa only [mul_comm] using hc

theorem actual_rising_product_factorial (n k : ℕ) :
    (∏ i ∈ range n, ((k : ℚ) + (n : ℚ) + ((i : ℚ) + 1))) =
      ((k + 2 * n).factorial : ℚ) / ((k + n).factorial : ℚ) := by
  have h := ascending_product_factorial (k + n + 1) n (by omega)
  have htop : k + n + 1 + n - 1 = k + 2 * n := by omega
  have hbot : k + n + 1 - 1 = k + n := by omega
  rw [htop, hbot] at h
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using h

theorem actual_poleProduct_factorial (n k : ℕ) (hk : 1 ≤ k) :
    CoefficientMap.poleProduct n (k : ℚ) =
      ((k + n).factorial : ℚ) / ((k - 1).factorial : ℚ) := by
  have h := ascending_product_factorial k (n + 1) hk
  have htop : k + (n + 1) - 1 = k + n := by omega
  simpa only [CoefficientMap.poleProduct, htop] using h

theorem actualR_factorial (n k : ℕ) (hk : n < k) :
    CoefficientMap.actualR n (k : ℚ) =
      (n.factorial : ℚ) ^ 7 * ((k - 1).factorial : ℚ) ^ 10 *
        ((k + 2 * n).factorial : ℚ) /
      (((k - n - 1).factorial : ℚ) * ((k + n).factorial : ℚ) ^ 10) := by
  have hk1 : 1 ≤ k := by omega
  unfold CoefficientMap.actualR CoefficientMap.numerator
  rw [actual_falling_product_factorial n k hk,
    actual_rising_product_factorial n k, actual_poleProduct_factorial n k hk1]
  field_simp [rational_factorial_ne_zero]

theorem actualR_factorial_real (n k : ℕ) (hk : n < k) :
    (CoefficientMap.actualR n (k : ℚ) : ℝ) =
      (n.factorial : ℝ) ^ 7 * ((k - 1).factorial : ℝ) ^ 10 *
        ((k + 2 * n).factorial : ℝ) /
      (((k - n - 1).factorial : ℝ) * ((k + n).factorial : ℝ) ^ 10) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (actualR_factorial n k hk)
  push_cast at h
  exact h

theorem actualR_pos (n k : ℕ) (hk : n < k) :
    0 < CoefficientMap.actualR n (k : ℚ) := by
  rw [actualR_factorial n k hk]
  have h0 : (0 : ℚ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h1 : (0 : ℚ) < (k - 1).factorial := by
    exact_mod_cast Nat.factorial_pos (k - 1)
  have h2 : (0 : ℚ) < (k + 2 * n).factorial := by
    exact_mod_cast Nat.factorial_pos (k + 2 * n)
  have h3 : (0 : ℚ) < (k - n - 1).factorial := by
    exact_mod_cast Nat.factorial_pos (k - n - 1)
  have h4 : (0 : ℚ) < (k + n).factorial := by
    exact_mod_cast Nat.factorial_pos (k + n)
  positivity

theorem actualR_real_pos (n k : ℕ) (hk : n < k) :
    0 < (CoefficientMap.actualR n (k : ℚ) : ℝ) := by
  exact_mod_cast actualR_pos n k hk

/-- Exact log identity after removing the two predecessor factorials. -/
theorem actualR_log_factorial (n k : ℕ) (hk : n < k) :
    Real.log (CoefficientMap.actualR n (k : ℚ) : ℝ) =
      7 * Real.log (n.factorial : ℝ) + 10 * Real.log (k.factorial : ℝ) +
        Real.log ((k + 2 * n).factorial : ℝ) -
        Real.log ((k - n).factorial : ℝ) -
        10 * Real.log ((k + n).factorial : ℝ) -
        10 * Real.log (k : ℝ) + Real.log ((k - n : ℕ) : ℝ) := by
  have h0 := AnalyticFactorialBounds.real_factorial_pos n
  have h1 := AnalyticFactorialBounds.real_factorial_pos (k - 1)
  have h2 := AnalyticFactorialBounds.real_factorial_pos (k + 2 * n)
  have h3 := AnalyticFactorialBounds.real_factorial_pos (k - n - 1)
  have h4 := AnalyticFactorialBounds.real_factorial_pos (k + n)
  rw [actualR_factorial_real n k hk,
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) h2.ne',
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul h3.ne' (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
  rw [AnalyticFactorialBounds.log_factorial_pred k (by omega)]
  have hpred : k - n - 1 = (k - n) - 1 := by omega
  rw [hpred, AnalyticFactorialBounds.log_factorial_pred (k - n) (by omega)]
  ring

end ZetaNine.AnalyticRationalFactorial

#print axioms ZetaNine.AnalyticRationalFactorial.ascending_product_factorial
#print axioms ZetaNine.AnalyticRationalFactorial.actual_falling_product_factorial
#print axioms ZetaNine.AnalyticRationalFactorial.actual_rising_product_factorial
#print axioms ZetaNine.AnalyticRationalFactorial.actual_poleProduct_factorial
#print axioms ZetaNine.AnalyticRationalFactorial.actualR_factorial
#print axioms ZetaNine.AnalyticRationalFactorial.actualR_factorial_real
#print axioms ZetaNine.AnalyticRationalFactorial.actualR_pos
#print axioms ZetaNine.AnalyticRationalFactorial.actualR_real_pos
#print axioms ZetaNine.AnalyticRationalFactorial.actualR_log_factorial


/- SOURCE module: missions.zeta9.formalization.AnalyticPhase; complete theorem bodies retained. -/

/-!
UNCOMPILED preparation for the actual phase in round7/research/analytic.md.
The phase, ratio and derivative are actual functions, not assumed bounds.
This does not yet establish the moment asymptotic, uniform o(1), or Z9.A.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Set

namespace ZetaNine.AnalyticPhase









theorem phaseGap_identity (x : ℝ) :
    (x - 1) * (x + 1) ^ 10 - (x + 2) * x ^ 10 =
    (743876235460997060507 / 100000000000000000000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 0 +
    (109589356802878649457 / 100000000000000000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 1 +
    (10634683646357555663 / 2000000000000000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 2 +
    (29280046551142071 / 2500000000000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 3 +
    (1524457114482447 / 100000000000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 4 +
    (32277046531191 / 2500000000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 5 +
    (73792828347 / 10000000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 6 +
    (71169471 / 25000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 7 +
    (1428963 / 2000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 8 +
    (1057 / 10 : ℝ) * (x - (101 / 100 : ℝ)) ^ 9 +
    (7 / 1 : ℝ) * (x - (101 / 100 : ℝ)) ^ 10 := by
  ring

theorem phaseGap_pos (x : ℝ) (hx : (101 / 100 : ℝ) ≤ x) :
    0 < (x - 1) * (x + 1) ^ 10 - (x + 2) * x ^ 10 := by
  rw [phaseGap_identity]
  have hy : 0 ≤ x - (101 / 100 : ℝ) := sub_nonneg.mpr hx
  positivity

theorem phaseRatio_pos (x : ℝ) (hx : 1 < x) : 0 < phaseRatio x := by
  unfold phaseRatio
  have hx0 : 0 < x := by linarith
  have hxm : 0 < x - 1 := by linarith
  have hxp : 0 < x + 1 := by linarith
  have hx2 : 0 < x + 2 := by linarith
  positivity

theorem phaseRatio_lt_one (x : ℝ) (hx : (101 / 100 : ℝ) ≤ x) :
    phaseRatio x < 1 := by
  have hx0 : 0 < x := by linarith
  have hxm : 0 < x - 1 := by linarith
  have hxp : 0 < x + 1 := by linarith
  have hd : 0 < (x - 1) * (x + 1) ^ 10 := by positivity
  unfold phaseRatio
  apply (div_lt_one hd).mpr
  exact sub_pos.mp (phaseGap_pos x hx)

theorem phaseSlope_eq_log_ratio (x : ℝ) (hx : 1 < x) :
    phaseSlope x = Real.log (phaseRatio x) := by
  have hx0 : x ≠ 0 := ne_of_gt (by linarith : 0 < x)
  have hxm : x - 1 ≠ 0 := ne_of_gt (by linarith : 0 < x - 1)
  have hxp : x + 1 ≠ 0 := ne_of_gt (by linarith : 0 < x + 1)
  have hx2 : x + 2 ≠ 0 := ne_of_gt (by linarith : 0 < x + 2)
  unfold phaseSlope phaseRatio
  rw [Real.log_div (mul_ne_zero hx2 (pow_ne_zero 10 hx0))
    (mul_ne_zero hxm (pow_ne_zero 10 hxp)),
    Real.log_mul hx2 (pow_ne_zero 10 hx0),
    Real.log_mul hxm (pow_ne_zero 10 hxp), Real.log_pow, Real.log_pow]
  ring

theorem phaseSlope_neg_right (x : ℝ) (hx : (101 / 100 : ℝ) ≤ x) :
    phaseSlope x < 0 := by
  have hx1 : 1 < x := by linarith
  rw [phaseSlope_eq_log_ratio x hx1]
  exact Real.log_neg (phaseRatio_pos x hx1) (phaseRatio_lt_one x hx)

theorem hasDerivAt_mul_log_shift (x a : ℝ) (ha : x + a ≠ 0) :
    HasDerivAt (fun y : ℝ => (y + a) * Real.log (y + a))
      (Real.log (x + a) + 1) x := by
  have h := ((hasDerivAt_id x).add_const a).mul
    (((hasDerivAt_id x).add_const a).log ha)
  convert h using 1
  all_goals first | rfl | simp [id_eq, one_div, mul_inv_cancel₀ ha]


theorem phase_hasDerivAt (x : ℝ) (hx : 1 < x) :
    HasDerivAt phase (phaseSlope x) x := by
  have h0 : x + 0 ≠ 0 := by linarith
  have h2 : x + 2 ≠ 0 := by linarith
  have hm : x + (-1) ≠ 0 := by linarith
  have hp : x + 1 ≠ 0 := by linarith
  have h := (((hasDerivAt_mul_log_shift x 0 h0).const_mul 10).add
    (hasDerivAt_mul_log_shift x 2 h2)).sub
    (hasDerivAt_mul_log_shift x (-1) hm)
  have h' := h.sub ((hasDerivAt_mul_log_shift x 1 hp).const_mul 10)
  convert h' using 1
  all_goals first | rfl | (funext y; simp [phase, Pi.neg_apply, sub_eq_add_neg]; ring) | (simp [phaseSlope, id_eq, sub_eq_add_neg]; ring)


theorem deriv_phase (x : ℝ) (hx : 1 < x) : deriv phase x = phaseSlope x :=
  (phase_hasDerivAt x hx).deriv

theorem phase_strictAntiOn_right : StrictAntiOn phase (Ici (101 / 100 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici (101 / 100 : ℝ))
  · intro x hx
    have hx1 : 1 < x := by have h : (101 / 100 : ℝ) ≤ x := hx; linarith
    exact (phase_hasDerivAt x hx1).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : (101 / 100 : ℝ) ≤ x := interior_subset hx
    rw [deriv_phase x (by linarith : 1 < x)]
    exact phaseSlope_neg_right x hx'

theorem phase_le_right_endpoint (x : ℝ) (hx : (101 / 100 : ℝ) ≤ x) :
    phase x ≤ phase (101 / 100) := by
  have h0 : (101 / 100 : ℝ) ∈ Ici (101 / 100 : ℝ) := by
    change (101 / 100 : ℝ) ≤ (101 / 100 : ℝ)
    exact le_rfl
  exact phase_strictAntiOn_right.antitoneOn h0 hx hx


theorem upperSlopeConstant_pos : 0 < upperSlopeConstant := by
  norm_num [upperSlopeConstant]

theorem upperSlopeConstant_eq : upperSlopeConstant =
    (33249125974877255751301 / 10763674952097696180200100 : ℝ) := by
  norm_num [upperSlopeConstant]

theorem phaseRatio_small_interval_le (u : ℝ) (hu : 0 < u)
    (hu1 : u ≤ (1 / 100 : ℝ)) : phaseRatio (1 + u) ≤ upperSlopeConstant / u := by
  have h2 : 0 < 2 + u := by linarith
  have hb : (1 + u) / (2 + u) ≤ (101 / 201 : ℝ) := by
    apply (div_le_iff₀ h2).mpr
    nlinarith
  have hb0 : 0 ≤ (1 + u) / (2 + u) := by positivity
  have hp : ((1 + u) / (2 + u)) ^ 10 ≤ (101 / 201 : ℝ) ^ 10 :=
    pow_le_pow_left₀ hb0 hb 10
  have hc : 3 + u ≤ (301 / 100 : ℝ) := by linarith
  have hm : (3 + u) * ((1 + u) / (2 + u)) ^ 10 ≤ upperSlopeConstant := by
    unfold upperSlopeConstant
    exact mul_le_mul hc hp (by positivity) (by norm_num)
  have he : phaseRatio (1 + u) = ((3 + u) * ((1 + u) / (2 + u)) ^ 10) / u := by
    unfold phaseRatio
    field_simp [ne_of_gt hu, ne_of_gt h2]
    ring
  rw [he]
  exact div_le_div_of_nonneg_right hm (le_of_lt hu)

theorem phaseSlope_small_interval_le (u : ℝ) (hu : 0 < u)
    (hu1 : u ≤ (1 / 100 : ℝ)) : phaseSlope (1 + u) ≤ Real.log (upperSlopeConstant / u) := by
  have hx : 1 < 1 + u := by linarith
  rw [phaseSlope_eq_log_ratio (1 + u) hx]
  exact Real.log_le_log (phaseRatio_pos (1 + u) hx) (phaseRatio_small_interval_le u hu hu1)

end ZetaNine.AnalyticPhase


/- SOURCE module: AnalyticPhaseUpperBound; complete theorem bodies retained. -/

/-!
UNCOMPILED full-source candidate for the global actual phase bound.

The imported AnalyticPhase source is itself an unchanged UNCOMPILED preparation.
No Lean execution, kernel verification, moment asymptotic, uniform error estimate
or complete Z9.A result is claimed by this source-only preparation.

The numerical steps use Real.sum_range_le_log_div and
Real.log_div_le_sum_range_add, whose finite sums and remainders are already
proved in the pinned Mathlib source. All displayed constants are rational.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open Set
open scoped BigOperators

namespace ZetaNine.AnalyticPhase

/-- The actual smooth remainder, with the singular `(x-1) log(x-1)` removed. -/






theorem phase_one_eq : phase 1 = 3 * Real.log 3 - 20 * Real.log 2 := by
  norm_num [phase] <;> ring

theorem smoothPhaseGap_one : smoothPhaseGap 1 = 0 := by
  norm_num [smoothPhaseGap, phase] <;> ring

theorem smoothPhaseGap_hasDerivAt (x : ℝ) (hx : 1 ≤ x) :
    HasDerivAt smoothPhaseGap (smoothPhaseSlope x) x := by
  have h0 : x + 0 ≠ 0 := by linarith
  have h2 : x + 2 ≠ 0 := by linarith
  have hp : x + 1 ≠ 0 := by linarith
  have hmain :=
    ((((hasDerivAt_mul_log_shift x 0 h0).const_mul 10).add
      (hasDerivAt_mul_log_shift x 2 h2)).sub
        ((hasDerivAt_mul_log_shift x 1 hp).const_mul 10)).sub_const (phase 1)
  have hlinear := ((hasDerivAt_id x).sub_const 1).mul_const
    (1 + Real.log upperSlopeConstant)
  have h := hmain.sub hlinear
  convert h using 1
  all_goals first | rfl | (funext y; simp [smoothPhaseGap, id_eq, Pi.neg_apply, sub_eq_add_neg]; ring) | (simp [smoothPhaseSlope, id_eq, sub_eq_add_neg]; ring)

theorem smoothPhaseRatio_pos (x : ℝ) (hx : 1 ≤ x) :
    0 < smoothPhaseRatio x := by
  unfold smoothPhaseRatio
  have hx0 : 0 < x := by linarith
  have hp : 0 < x + 1 := by linarith
  have h2 : 0 < x + 2 := by linarith
  positivity

theorem smoothPhaseRatio_le_upperSlopeConstant (x : ℝ)
    (hx : x ∈ Icc (1 : ℝ) (101 / 100 : ℝ)) :
    smoothPhaseRatio x ≤ upperSlopeConstant := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hp : 0 < x + 1 := by linarith [hx.1]
  have hb : x / (x + 1) ≤ (101 / 201 : ℝ) := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [hx.2]
  have hb0 : 0 ≤ x / (x + 1) := le_of_lt (div_pos hx0 hp)
  have hpow : (x / (x + 1)) ^ 10 ≤ (101 / 201 : ℝ) ^ 10 :=
    pow_le_pow_left₀ hb0 hb 10
  have hc : x + 2 ≤ (301 / 100 : ℝ) := by linarith [hx.2]
  unfold smoothPhaseRatio upperSlopeConstant
  exact mul_le_mul hc hpow (by positivity) (by norm_num)

theorem smoothPhaseSlope_eq_log_ratio (x : ℝ) (hx : 1 ≤ x) :
    smoothPhaseSlope x =
      Real.log (smoothPhaseRatio x) - Real.log upperSlopeConstant := by
  have hx0 : 0 < x := by linarith
  have hp : 0 < x + 1 := by linarith
  have h2 : 0 < x + 2 := by linarith
  have hr : 0 < x / (x + 1) := div_pos hx0 hp
  unfold smoothPhaseSlope smoothPhaseRatio
  rw [Real.log_mul (ne_of_gt h2) (pow_ne_zero 10 (ne_of_gt hr)),
    Real.log_pow, Real.log_div (ne_of_gt hx0) (ne_of_gt hp)]
  norm_num <;> ring

theorem smoothPhaseSlope_nonpos (x : ℝ)
    (hx : x ∈ Icc (1 : ℝ) (101 / 100 : ℝ)) :
    smoothPhaseSlope x ≤ 0 := by
  rw [smoothPhaseSlope_eq_log_ratio x hx.1]
  exact sub_nonpos.mpr (Real.log_le_log (smoothPhaseRatio_pos x hx.1)
    (smoothPhaseRatio_le_upperSlopeConstant x hx))

theorem smoothPhaseGap_antitoneOn :
    AntitoneOn smoothPhaseGap (Icc (1 : ℝ) (101 / 100 : ℝ)) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := smoothPhaseSlope) (convex_Icc (1 : ℝ) (101 / 100 : ℝ)) ?_ ?_ ?_
  · intro x hx
    exact (smoothPhaseGap_hasDerivAt x hx.1).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Icc (1 : ℝ) (101 / 100 : ℝ) := interior_subset hx
    exact (smoothPhaseGap_hasDerivAt x hx'.1).hasDerivWithinAt
  · intro x hx
    have hx' : x ∈ Icc (1 : ℝ) (101 / 100 : ℝ) := interior_subset hx
    exact smoothPhaseSlope_nonpos x hx'

theorem smoothPhaseGap_le_zero (x : ℝ)
    (hx : x ∈ Icc (1 : ℝ) (101 / 100 : ℝ)) :
    smoothPhaseGap x ≤ 0 := by
  have h1 : (1 : ℝ) ∈ Icc (1 : ℝ) (101 / 100 : ℝ) := by
    constructor <;> norm_num
  have h := smoothPhaseGap_antitoneOn h1 hx hx.1
  simpa only [smoothPhaseGap_one] using h

/-- The universal elementary cap; its hypotheses assert only positivity. -/
theorem mul_one_add_log_div_le (a u : ℝ) (ha : 0 < a) (hu : 0 < u) :
    u * (1 + Real.log (a / u)) ≤ a := by
  have hlog := Real.log_le_sub_one_of_pos (div_pos ha hu)
  have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hu)
  have he : u * (a / u - 1) = a - u := by
    field_simp [ne_of_gt hu]
  calc
    u * (1 + Real.log (a / u)) = u + u * Real.log (a / u) := by ring
    _ ≤ u + u * (a / u - 1) := add_le_add (le_refl u) hmul
    _ = a := by rw [he]; ring

theorem phase_small_interval_identity (u : ℝ) (hu : 0 < u) :
    phase (1 + u) = phase 1 +
      u * (1 + Real.log (upperSlopeConstant / u)) + smoothPhaseGap (1 + u) := by
  rw [Real.log_div (ne_of_gt upperSlopeConstant_pos) (ne_of_gt hu)]
  unfold smoothPhaseGap phase
  have he : (1 + u : ℝ) - 1 = u := by ring
  simp only [he]
  ring

theorem phase_small_interval_le_one_add_constant (u : ℝ) (hu : 0 < u)
    (hu1 : u ≤ (1 / 100 : ℝ)) :
    phase (1 + u) ≤ phase 1 + upperSlopeConstant := by
  have hx : (1 + u : ℝ) ∈ Icc (1 : ℝ) (101 / 100 : ℝ) := by
    constructor <;> linarith
  have hgap := smoothPhaseGap_le_zero (1 + u) hx
  have hcap := mul_one_add_log_div_le upperSlopeConstant u upperSlopeConstant_pos hu
  rw [phase_small_interval_identity u hu]
  linarith

theorem phase_global_le_one_add_constant (x : ℝ) (hx : 1 < x) :
    phase x ≤ phase 1 + upperSlopeConstant := by
  by_cases hsmall : x ≤ (101 / 100 : ℝ)
  · have hu : 0 < x - 1 := by linarith
    have hu1 : x - 1 ≤ (1 / 100 : ℝ) := by linarith
    have h := phase_small_interval_le_one_add_constant (x - 1) hu hu1
    have he : (1 + (x - 1) : ℝ) = x := by ring
    simpa only [he] using h
  · have hright : (101 / 100 : ℝ) ≤ x := by linarith
    have hendpoint := phase_small_interval_le_one_add_constant (1 / 100)
      (by norm_num) (by norm_num)
    have he : (1 + (1 / 100) : ℝ) = 101 / 100 := by norm_num
    rw [he] at hendpoint
    exact (phase_le_right_endpoint x hright).trans hendpoint

/-- Six terms at `1/3`; the lower rational margin is strictly positive. -/
theorem log_two_lower_rational : (693147 / 1000000 : ℝ) < Real.log 2 := by
  have h := Real.sum_range_le_log_div (x := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) 6
  have harg : (1 + (1 / 3 : ℝ)) / (1 - (1 / 3 : ℝ)) = 2 := by norm_num
  rw [harg] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- Eleven terms at `1/2`, using the actual proved Mathlib geometric remainder. -/
theorem log_three_upper_rational : Real.log 3 < (1098613 / 1000000 : ℝ) := by
  have h := Real.log_div_le_sum_range_add (x := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) 11
  have harg : (1 + (1 / 2 : ℝ)) / (1 - (1 / 2 : ℝ)) = 3 := by norm_num
  rw [harg] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem upperSlopeConstant_lt_rational :
    upperSlopeConstant < (309 / 100000 : ℝ) := by
  norm_num [upperSlopeConstant]

theorem phase_one_add_constant_lt_certified :
    phase 1 + upperSlopeConstant < (-10564011 / 1000000 : ℝ) := by
  rw [phase_one_eq]
  have h2 := log_two_lower_rational
  have h3 := log_three_upper_rational
  have hA := upperSlopeConstant_lt_rational
  linarith

/-- Stronger rational margin, without any finite sampling of the phase. -/
theorem phase_global_lt_certified (x : ℝ) (hx : 1 < x) :
    phase x < (-10564011 / 1000000 : ℝ) :=
  (phase_global_le_one_add_constant x hx).trans_lt phase_one_add_constant_lt_certified

/-- The actual requested whole-domain phase component, with its exact open domain. -/
theorem phase_global_upper_bound :
    ∀ x : ℝ, 1 < x → phase x ≤ (-2641 / 250 : ℝ) := by
  intro x hx
  have h := phase_global_lt_certified x hx
  linarith

end ZetaNine.AnalyticPhase


/- SOURCE module: AnalyticRationalLogBound; complete theorem bodies retained. -/

/-!
UNCOMPILED SOURCE preparation. Private compilation must use the already
verified native-export AnalyticPhase / AnalyticPhaseUpperBound dependencies,
not the unchanged historical shared preparations with the same module names.

This is a pointwise bound for the actual product-defined rational function.
The full infinite moment estimate still requires a quantitative p-series tail
bound and the finite compact/tail summation argument.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section

namespace ZetaNine.AnalyticRationalLogBound

theorem scaled_phase_identity (n k : ℝ) (hn : 0 < n) (hk : n < k) :
    7 * n * Real.log n + 10 * k * Real.log k +
      (k + 2 * n) * Real.log (k + 2 * n) -
      (k - n) * Real.log (k - n) -
      10 * (k + n) * Real.log (k + n) =
      n * AnalyticPhase.phase (k / n) := by
  have hk0 : 0 < k := lt_trans hn hk
  have hkm : 0 < k - n := sub_pos.mpr hk
  have hkp : 0 < k + n := by positivity
  have hk2 : 0 < k + 2 * n := by positivity
  have he2 : k / n + 2 = (k + 2 * n) / n := by
    field_simp [hn.ne']
  have hem : k / n - 1 = (k - n) / n := by
    field_simp [hn.ne']
  have hep : k / n + 1 = (k + n) / n := by
    field_simp [hn.ne']
  unfold AnalyticPhase.phase
  rw [he2, hem, hep, Real.log_div hk0.ne' hn.ne',
    Real.log_div hk2.ne' hn.ne', Real.log_div hkm.ne' hn.ne',
    Real.log_div hkp.ne' hn.ne']
  field_simp [hn.ne']
  ring

/-- The exact residual log terms and constant are 7 log n, log(k+2n),
log(k-n), and 18. The factorial shifts have already been eliminated exactly. -/
theorem actualR_log_le_phase (n k : ℕ) (hn : 1 ≤ n) (hk : n < k) :
    Real.log (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      (n : ℝ) * AnalyticPhase.phase ((k : ℝ) / (n : ℝ)) +
        7 * Real.log (n : ℝ) + Real.log ((k : ℝ) + 2 * (n : ℝ)) +
        Real.log ((k : ℝ) - (n : ℝ)) + 18 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkn : (n : ℝ) < k := by exact_mod_cast hk
  have hnupper := AnalyticFactorialBounds.log_factorial_upper n hn
  have hkupper := AnalyticFactorialBounds.log_factorial_upper k (by omega)
  have hk2upper := AnalyticFactorialBounds.log_factorial_upper (k + 2 * n) (by omega)
  have hkmnlower := AnalyticFactorialBounds.log_factorial_lower (k - n)
  have hkplower := AnalyticFactorialBounds.log_factorial_lower (k + n)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_sub (Nat.le_of_lt hk)] at hk2upper hkmnlower hkplower
  rw [AnalyticRationalFactorial.actualR_log_factorial n k hk]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_sub (Nat.le_of_lt hk)]
  have hphase := scaled_phase_identity (n : ℝ) (k : ℝ) hn0 hkn
  nlinarith

theorem actualR_log_le_certified (n k : ℕ) (hn : 1 ≤ n) (hk : n < k) :
    Real.log (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      -(2641 / 250 : ℝ) * n + 7 * Real.log (n : ℝ) +
        Real.log ((k : ℝ) + 2 * (n : ℝ)) +
        Real.log ((k : ℝ) - (n : ℝ)) + 18 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkn : (n : ℝ) < k := by exact_mod_cast hk
  have hratio : 1 < (k : ℝ) / (n : ℝ) := (one_lt_div hn0).mpr hkn
  have hphase := AnalyticPhase.phase_global_upper_bound _ hratio
  have hmul := mul_le_mul_of_nonneg_left hphase hn0.le
  have h := actualR_log_le_phase n k hn hk
  nlinarith

/-- Exponentiating the genuine log bound gives an explicit polynomial factor. -/
theorem actualR_le_certified (n k : ℕ) (hn : 1 ≤ n) (hk : n < k) :
    (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      Real.exp 18 * (n : ℝ) ^ 7 * ((k : ℝ) + 2 * (n : ℝ)) *
        ((k : ℝ) - (n : ℝ)) * Real.exp (-(2641 / 250 : ℝ) * n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkn : (n : ℝ) < k := by exact_mod_cast hk
  have hkm : (0 : ℝ) < (k : ℝ) - (n : ℝ) := sub_pos.mpr hkn
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 * (n : ℝ) := by linarith
  have hR := AnalyticRationalFactorial.actualR_real_pos n k hk
  have h := (Real.log_le_iff_le_exp hR).mp (actualR_log_le_certified n k hn hk)
  have he :
      Real.exp (-(2641 / 250 : ℝ) * n + 7 * Real.log (n : ℝ) +
        Real.log ((k : ℝ) + 2 * (n : ℝ)) +
        Real.log ((k : ℝ) - (n : ℝ)) + 18) =
      Real.exp 18 * (n : ℝ) ^ 7 * ((k : ℝ) + 2 * (n : ℝ)) *
        ((k : ℝ) - (n : ℝ)) * Real.exp (-(2641 / 250 : ℝ) * n) := by
    rw [show 7 * Real.log (n : ℝ) = Real.log ((n : ℝ) ^ 7) by
      simpa only [Nat.cast_ofNat] using (Real.log_pow (n : ℝ) 7).symm]
    simp only [Real.exp_add, Real.exp_log (pow_pos hn0 7),
      Real.exp_log hk2, Real.exp_log hkm]
    ring
  exact h.trans_eq he

theorem actualR_compact_bound (n k : ℕ) (hn : 1 ≤ n)
    (hk : n < k) (hk2 : k ≤ 2 * n) :
    (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      4 * Real.exp 18 * (n : ℝ) ^ 9 * Real.exp (-(2641 / 250 : ℝ) * n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkn : (n : ℝ) < k := by exact_mod_cast hk
  have hk2r : (k : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hk2
  have hprod : ((k : ℝ) + 2 * (n : ℝ)) * ((k : ℝ) - (n : ℝ)) ≤
      4 * (n : ℝ) ^ 2 := by
    have hleft : (k : ℝ) + 2 * (n : ℝ) ≤ 4 * (n : ℝ) := by linarith
    have hright : (k : ℝ) - (n : ℝ) ≤ (n : ℝ) := by linarith
    have h := mul_le_mul hleft hright (by linarith : (0 : ℝ) ≤ (k : ℝ) - n)
      (by positivity : (0 : ℝ) ≤ 4 * (n : ℝ))
    nlinarith
  calc
    (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
        Real.exp 18 * (n : ℝ) ^ 7 *
          (((k : ℝ) + 2 * (n : ℝ)) * ((k : ℝ) - (n : ℝ))) *
          Real.exp (-(2641 / 250 : ℝ) * n) := by
      simpa only [mul_assoc] using actualR_le_certified n k hn hk
    _ ≤ Real.exp 18 * (n : ℝ) ^ 7 * (4 * (n : ℝ) ^ 2) *
          Real.exp (-(2641 / 250 : ℝ) * n) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hprod (by positivity)) (Real.exp_pos _).le
    _ = _ := by ring

end ZetaNine.AnalyticRationalLogBound

#print axioms ZetaNine.AnalyticRationalLogBound.scaled_phase_identity
#print axioms ZetaNine.AnalyticRationalLogBound.actualR_log_le_phase
#print axioms ZetaNine.AnalyticRationalLogBound.actualR_log_le_certified
#print axioms ZetaNine.AnalyticRationalLogBound.actualR_le_certified
#print axioms ZetaNine.AnalyticRationalLogBound.actualR_compact_bound


/- SOURCE module: AnalyticRationalTail; complete theorem bodies retained. -/

/-!
UNCOMPILED SOURCE preparation. Direct product bound for the actual tail
k >= 2n, n >= 1. No factorial-formula assumption, summability assumption,
Stirling asymptotic, or infinite-tail estimate is introduced.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section
open scoped BigOperators
open Finset

namespace ZetaNine.AnalyticRationalTail

theorem actual_falling_product_le (n k : ℕ) (hk : n < k) :
    (∏ i ∈ range n, ((k : ℚ) - ((i : ℚ) + 1))) ≤ (k : ℚ) ^ n := by
  calc
    _ ≤ ∏ _i ∈ range n, (k : ℚ) := by
      apply Finset.prod_le_prod
      · intro i hi
        have hi1 : i + 1 ≤ k := by have := mem_range.mp hi; omega
        have hir : (i : ℚ) + 1 ≤ (k : ℚ) := by exact_mod_cast hi1
        linarith
      · intro i hi
        have hi0 : (0 : ℚ) ≤ i := by positivity
        linarith
    _ = _ := by simp

theorem actual_rising_product_tail_le (n k : ℕ) (hk : 2 * n ≤ k) :
    (∏ i ∈ range n, ((k : ℚ) + (n : ℚ) + ((i : ℚ) + 1))) ≤
      (2 * (k : ℚ)) ^ n := by
  calc
    _ ≤ ∏ _i ∈ range n, (2 * (k : ℚ)) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        have hi1 : n + i + 1 ≤ k := by have := mem_range.mp hi; omega
        have hir : (n : ℚ) + (i : ℚ) + 1 ≤ (k : ℚ) := by exact_mod_cast hi1
        linarith
    _ = _ := by simp

theorem actual_poleProduct_ge (n k : ℕ) :
    (k : ℚ) ^ (n + 1) ≤ CoefficientMap.poleProduct n (k : ℚ) := by
  unfold CoefficientMap.poleProduct
  calc
    (k : ℚ) ^ (n + 1) = ∏ _i ∈ range (n + 1), (k : ℚ) := by simp
    _ ≤ ∏ i ∈ range (n + 1), ((k : ℚ) + i) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        exact le_add_of_nonneg_right (Nat.cast_nonneg i)

theorem actualR_tail_bound_rational (n k : ℕ) (hn : 1 ≤ n) (hk : 2 * n ≤ k) :
    CoefficientMap.actualR n (k : ℚ) ≤
      (n.factorial : ℚ) ^ 7 * (2 : ℚ) ^ n / (k : ℚ) ^ (7 * n + 9) := by
  have hkn : n < k := by omega
  have hk0 : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
  have hfac : (0 : ℚ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hfall := actual_falling_product_le n k hkn
  have hrise := actual_rising_product_tail_le n k hk
  have hfall0 :
      0 ≤ ∏ i ∈ range n, ((k : ℚ) - ((i : ℚ) + 1)) := by
    apply Finset.prod_nonneg
    intro i hi
    have hi1 : i + 1 ≤ k := by have := mem_range.mp hi; omega
    have hir : (i : ℚ) + 1 ≤ (k : ℚ) := by exact_mod_cast hi1
    linarith
  have hrise0 :
      0 ≤ ∏ i ∈ range n, ((k : ℚ) + (n : ℚ) + ((i : ℚ) + 1)) := by
    apply Finset.prod_nonneg
    intro i hi
    positivity
  have hnum : CoefficientMap.numerator n (k : ℚ) ≤
      (n.factorial : ℚ) ^ 7 * (k : ℚ) ^ n * (2 * (k : ℚ)) ^ n := by
    unfold CoefficientMap.numerator
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hfall (by positivity)) hrise hrise0 (by positivity)
  have hbase := actual_poleProduct_ge n k
  have hbase0 : (0 : ℚ) < (k : ℚ) ^ (n + 1) := by positivity
  have hpole0 : (0 : ℚ) < CoefficientMap.poleProduct n (k : ℚ) :=
    lt_of_lt_of_le hbase0 hbase
  have hden := pow_le_pow_left₀ hbase0.le hbase 9
  have hpow : ((k : ℚ) ^ (n + 1)) ^ 9 =
      (k : ℚ) ^ (7 * n + 9) * (k : ℚ) ^ n * (k : ℚ) ^ n := by
    rw [← pow_mul, ← pow_add, ← pow_add]
    congr 1
    omega
  unfold CoefficientMap.actualR
  calc
    CoefficientMap.numerator n (k : ℚ) /
        CoefficientMap.poleProduct n (k : ℚ) ^ 9 ≤
      ((n.factorial : ℚ) ^ 7 * (k : ℚ) ^ n * (2 * (k : ℚ)) ^ n) /
        CoefficientMap.poleProduct n (k : ℚ) ^ 9 :=
      div_le_div_of_nonneg_right hnum (pow_pos hpole0 9).le
    _ ≤ ((n.factorial : ℚ) ^ 7 * (k : ℚ) ^ n * (2 * (k : ℚ)) ^ n) /
        ((k : ℚ) ^ (n + 1)) ^ 9 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by
      rw [mul_pow, hpow]
      field_simp [hk0.ne']

theorem actualR_tail_bound (n k : ℕ) (hn : 1 ≤ n) (hk : 2 * n ≤ k) :
    (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      (n.factorial : ℝ) ^ 7 * (2 : ℝ) ^ n / (k : ℝ) ^ (7 * n + 9) := by
  have h := actualR_tail_bound_rational n k hn hk
  have hc : (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      (( (n.factorial : ℚ) ^ 7 * (2 : ℚ) ^ n / (k : ℚ) ^ (7 * n + 9) : ℚ) : ℝ) := by
    exact_mod_cast h
  push_cast at hc
  exact hc

theorem actual_tail_weight_le (n k : ℕ) (hk : 2 * n ≤ k) :
    (k : ℝ) * ((k : ℝ) + (n : ℝ)) ≤ (3 / 2 : ℝ) * (k : ℝ) ^ 2 := by
  have h : 2 * (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  nlinarith

end ZetaNine.AnalyticRationalTail

#print axioms ZetaNine.AnalyticRationalTail.actual_falling_product_le
#print axioms ZetaNine.AnalyticRationalTail.actual_rising_product_tail_le
#print axioms ZetaNine.AnalyticRationalTail.actual_poleProduct_ge
#print axioms ZetaNine.AnalyticRationalTail.actualR_tail_bound_rational
#print axioms ZetaNine.AnalyticRationalTail.actualR_tail_bound
#print axioms ZetaNine.AnalyticRationalTail.actual_tail_weight_le


/- SOURCE module: AnalyticPSeriesTail; complete theorem bodies retained. -/

/-!
UNCOMPILED SOURCE preparation. Quantitative tail for a genuine reciprocal
natural power series. Summability and the integral comparison are proved
from M >= 1 and s >= 2; neither is an input hypothesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section
open scoped BigOperators
open Set MeasureTheory Finset

namespace ZetaNine.AnalyticPSeriesTail

theorem nat_negative_rpow_eq_reciprocal_pow (k s : ℕ) :
    (k : ℝ) ^ (-(s : ℝ)) = 1 / (k : ℝ) ^ s := by
  rw [Real.rpow_neg (Nat.cast_nonneg k), Real.rpow_natCast, one_div]

theorem reciprocal_power_tail_summable (M s : ℕ) (hs : 2 ≤ s) :
    Summable (fun i : ℕ => 1 / ((i + M : ℕ) : ℝ) ^ s) := by
  exact (Real.summable_one_div_nat_pow.mpr (by omega : 1 < s)).comp_injective
    (fun _i _j h => Nat.add_right_cancel h)

theorem reciprocal_power_tail_bound (M s : ℕ) (hM : 1 ≤ M) (hs : 2 ≤ s) :
    (∑' i : ℕ, 1 / ((i + M : ℕ) : ℝ) ^ s) ≤
      1 / (M : ℝ) ^ s + 1 / (M : ℝ) ^ (s - 1) / ((s - 1 : ℕ) : ℝ) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hs0 : (0 : ℝ) < ((s - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < s - 1 by omega)
  have hsneg : -(s : ℝ) < -1 := by
    have h : (1 : ℝ) < s := by exact_mod_cast (show 1 < s by omega)
    linarith
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-(s : ℝ))) (Ici (M : ℝ)) := by
    apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by have h : (0 : ℝ) ≤ s := Nat.cast_nonneg s; linarith)).mono
    intro x hx
    exact lt_of_lt_of_le hM0 hx
  have hint : IntegrableOn (fun x : ℝ => x ^ (-(s : ℝ))) (Ioi (M : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt hsneg hM0
  have hnonneg : ∀ x ∈ Ioi (M : ℝ), 0 ≤ x ^ (-(s : ℝ)) := by
    intro x hx
    exact Real.rpow_nonneg (lt_trans hM0 hx).le _
  have htail := AntitoneOn.tsum_comp_add_le_integral M hanti hint hnonneg
  have heval := integral_Ioi_rpow_of_lt hsneg hM0
  have he : -(s : ℝ) + 1 = -((s - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one]
    ring
  have heval' : (∫ x : ℝ in Ioi (M : ℝ), x ^ (-(s : ℝ))) =
      1 / (M : ℝ) ^ (s - 1) / ((s - 1 : ℕ) : ℝ) := by
    simpa only [he, nat_negative_rpow_eq_reciprocal_pow,
      div_neg, neg_div, neg_neg] using heval
  rw [heval'] at htail
  simp only [nat_negative_rpow_eq_reciprocal_pow] at htail
  have hsum := reciprocal_power_tail_summable M s hs
  have hsplit := hsum.sum_add_tsum_nat_add 1
  have hsplit' : (∑' i : ℕ, 1 / ((i + M : ℕ) : ℝ) ^ s) =
      1 / (M : ℝ) ^ s + (∑' i : ℕ, 1 / ((i + M + 1 : ℕ) : ℝ) ^ s) := by
    simpa only [sum_range_one, Nat.zero_add, Nat.add_zero, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using hsplit.symm
  rw [hsplit']
  exact add_le_add le_rfl htail

theorem reciprocal_power_tail_bound_factored (M s : ℕ) (hM : 1 ≤ M) (hs : 2 ≤ s) :
    (∑' i : ℕ, 1 / ((i + M : ℕ) : ℝ) ^ s) ≤
      1 / (M : ℝ) ^ s * (1 + (M : ℝ) / ((s - 1 : ℕ) : ℝ)) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hs0 : (0 : ℝ) < ((s - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < s - 1 by omega)
  have hindex : s = s - 1 + 1 := by omega
  have hpow : (M : ℝ) ^ s = (M : ℝ) ^ (s - 1) * (M : ℝ) := by
    calc
      (M : ℝ) ^ s = (M : ℝ) ^ (s - 1 + 1) := by rw [← hindex]
      _ = _ := pow_succ _ _
  have he : 1 / (M : ℝ) ^ s + 1 / (M : ℝ) ^ (s - 1) / ((s - 1 : ℕ) : ℝ) =
      1 / (M : ℝ) ^ s * (1 + (M : ℝ) / ((s - 1 : ℕ) : ℝ)) := by
    rw [hpow]
    field_simp [hM0.ne', hs0.ne']
  exact (reciprocal_power_tail_bound M s hM hs).trans_eq he

end ZetaNine.AnalyticPSeriesTail

#print axioms ZetaNine.AnalyticPSeriesTail.nat_negative_rpow_eq_reciprocal_pow
#print axioms ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_summable
#print axioms ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_bound
#print axioms ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_bound_factored


/- SOURCE module: AnalyticMomentBounds; complete theorem bodies retained. -/

/-!
UNCOMPILED SOURCE preparation. Actual raw moments, starting at k = m+1,
with the product's first n zero terms kept in the sequence. Summability is
proved by actual tail comparison rather than assumed or imported through
the partial-fraction / exactL proof chain.

This preparation reaches a genuine compact plus factorial-tail estimate.
The final exponential tail simplification and uniform changing-coefficient
estimate remain separate endpoints to add; this file does not assert Z9.A.
-/

set_option autoImplicit false
set_option maxHeartbeats 2600000

noncomputable section
open scoped BigOperators
open Finset

namespace ZetaNine.AnalyticMomentBounds











theorem actualR_zero_of_pos_le (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    CoefficientMap.actualR n (k : ℚ) = 0 := by
  have hpred : ((k - 1 : ℕ) : ℚ) + 1 = (k : ℚ) := by
    exact_mod_cast (Nat.sub_add_cancel hk)
  have hfall : (∏ i ∈ range n, ((k : ℚ) - ((i : ℚ) + 1))) = 0 := by
    apply Finset.prod_eq_zero (mem_range.mpr (by omega : k - 1 < n))
    rw [hpred]
    ring
  simp only [CoefficientMap.actualR, CoefficientMap.numerator, hfall,
    mul_zero, zero_mul, zero_div]

theorem actualMomentTerm_zero_of_pos_le (n r k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    actualMomentTerm n r k = 0 := by
  simp only [actualMomentTerm, actualR_zero_of_pos_le n k hk hkn,
    Rat.cast_zero, zero_mul]

theorem actualMomentTerm_nonneg (n r k : ℕ) (hk : 1 ≤ k) :
    0 ≤ actualMomentTerm n r k := by
  by_cases hkn : k ≤ n
  · rw [actualMomentTerm_zero_of_pos_le n r k hk hkn]
  · have hR := AnalyticRationalFactorial.actualR_real_pos n k (by omega : n < k)
    unfold actualMomentTerm
    positivity

theorem actualMomentSequence_nonneg (n r m : ℕ) :
    0 ≤ actualMomentSequence n r m :=
  actualMomentTerm_nonneg n r (m + 1) (by omega)

theorem actual_compact_weight_le (n k : ℕ) (hk : k ≤ 2 * n) :
    (k : ℝ) * ((k : ℝ) + (n : ℝ)) ≤ 6 * (n : ℝ) ^ 2 := by
  have h : (k : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hk
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hp := mul_le_mul h (by linarith : (k : ℝ) + n ≤ 3 * (n : ℝ))
    (by positivity : (0 : ℝ) ≤ (k : ℝ) + n)
    (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ))
  nlinarith

theorem actual_compact_momentTerm_bound (n r k : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4)
    (hk : n < k) (hk2 : k ≤ 2 * n) :
    actualMomentTerm n r k ≤
      5184 * Real.exp 18 * (n : ℝ) ^ 9 * (n : ℝ) ^ (2 * r) *
        Real.exp (-(2641 / 250 : ℝ) * n) := by
  have hR := AnalyticRationalLogBound.actualR_compact_bound n k hn hk hk2
  have hu := actual_compact_weight_le n k hk2
  have hu0 : (0 : ℝ) ≤ (k : ℝ) * ((k : ℝ) + n) := by positivity
  have hp := pow_le_pow_left₀ hu0 hu r
  have hterm := mul_le_mul hR hp (pow_nonneg hu0 r) (by positivity)
  have hc : 4 * (6 : ℝ) ^ r ≤ 5184 := by interval_cases r <;> norm_num
  have he :
      (4 * Real.exp 18 * (n : ℝ) ^ 9 * Real.exp (-(2641 / 250 : ℝ) * n)) *
        (6 * (n : ℝ) ^ 2) ^ r =
      (4 * (6 : ℝ) ^ r) *
        (Real.exp 18 * (n : ℝ) ^ 9 * (n : ℝ) ^ (2 * r) *
          Real.exp (-(2641 / 250 : ℝ) * n)) := by
    rw [mul_pow, ← pow_mul]
    ring
  unfold actualMomentTerm
  exact hterm.trans (he.le.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc (by positivity)))

theorem tailPower_ge (n r : ℕ) (hr : r ≤ 4) :
    7 * n + 1 ≤ tailPower n r := by
  unfold tailPower
  omega

theorem tailCoefficient_nonneg (n r : ℕ) : 0 ≤ tailCoefficient n r := by
  unfold tailCoefficient
  positivity

theorem actual_tail_momentTerm_bound (n r k : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4)
    (hk : 2 * n ≤ k) :
    actualMomentTerm n r k ≤ tailCoefficient n r / (k : ℝ) ^ tailPower n r := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hR := AnalyticRationalTail.actualR_tail_bound n k hn hk
  have hu := AnalyticRationalTail.actual_tail_weight_le n k hk
  have hu0 : (0 : ℝ) ≤ (k : ℝ) * ((k : ℝ) + n) := by positivity
  have hp := pow_le_pow_left₀ hu0 hu r
  have hterm := mul_le_mul hR hp (pow_nonneg hu0 r) (by positivity)
  have hindex : 7 * n + 9 = tailPower n r + 2 * r := by
    unfold tailPower
    omega
  have hpow : (k : ℝ) ^ (7 * n + 9) =
      (k : ℝ) ^ tailPower n r * (k : ℝ) ^ (2 * r) := by
    calc
      _ = (k : ℝ) ^ (tailPower n r + 2 * r) := congrArg (fun a : ℕ => (k : ℝ) ^ a) hindex
      _ = _ := pow_add _ _ _
  have he :
      ((n.factorial : ℝ) ^ 7 * (2 : ℝ) ^ n / (k : ℝ) ^ (7 * n + 9)) *
        ((3 / 2 : ℝ) * (k : ℝ) ^ 2) ^ r =
      tailCoefficient n r / (k : ℝ) ^ tailPower n r := by
    unfold tailCoefficient
    rw [mul_pow, ← pow_mul, hpow]
    field_simp [hk0.ne']
  unfold actualMomentTerm
  exact hterm.trans_eq he

theorem actualMomentSequence_summable (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    Summable (actualMomentSequence n r) := by
  have hs : 2 ≤ tailPower n r := by have := tailPower_ge n r hr; omega
  have hmajor : Summable (fun m : ℕ =>
      tailCoefficient n r / ((m + 2 * n : ℕ) : ℝ) ^ tailPower n r) := by
    simpa only [mul_one_div] using
      (AnalyticPSeriesTail.reciprocal_power_tail_summable (2 * n) (tailPower n r) hs).mul_left
        (tailCoefficient n r)
  have htail : Summable (fun m : ℕ => actualMomentSequence n r (m + (2 * n - 1))) := by
    apply Summable.of_nonneg_of_le
      (fun m => actualMomentSequence_nonneg n r (m + (2 * n - 1))) _ hmajor
    intro m
    have hindex : m + (2 * n - 1) + 1 = m + 2 * n := by omega
    simpa only [actualMomentSequence, hindex] using
      actual_tail_momentTerm_bound n r (m + 2 * n) hn hr (by omega)
  exact (summable_nat_add_iff (2 * n - 1)).mp htail

theorem actualMomentSequence_norm_summable (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    Summable (fun m : ℕ => ‖actualMomentSequence n r m‖) :=
  (actualMomentSequence_summable n r hn hr).norm

theorem actual_compact_moment_sum_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    (∑ m ∈ range (2 * n - 1), actualMomentSequence n r m) ≤
      5184 * Real.exp 18 * (n : ℝ) ^ 10 * (n : ℝ) ^ (2 * r) *
        Real.exp (-(2641 / 250 : ℝ) * n) := by
  have hindex : 2 * n - 1 = n + (n - 1) := by omega
  rw [hindex, Finset.sum_range_add]
  have hzero : (∑ m ∈ range n, actualMomentSequence n r m) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    exact actualMomentTerm_zero_of_pos_le n r (m + 1) (by omega)
      (by have := mem_range.mp hm; omega)
  rw [hzero, zero_add]
  let B : ℝ := 5184 * Real.exp 18 * (n : ℝ) ^ 9 * (n : ℝ) ^ (2 * r) *
    Real.exp (-(2641 / 250 : ℝ) * n)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc
    (∑ m ∈ range (n - 1), actualMomentSequence n r (n + m)) ≤
        ∑ _m ∈ range (n - 1), B := by
      apply Finset.sum_le_sum
      intro m hm
      have hm0 := mem_range.mp hm
      exact actual_compact_momentTerm_bound n r (n + m + 1) hn hr (by omega) (by omega)
    _ = ((n - 1 : ℕ) : ℝ) * B := by simp
    _ ≤ (n : ℝ) * B :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le n 1) hB
    _ = 5184 * Real.exp 18 * (n : ℝ) ^ 10 * (n : ℝ) ^ (2 * r) *
        Real.exp (-(2641 / 250 : ℝ) * n) := by dsimp [B]; ring

theorem actual_tail_moment_sum_factorial_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    (∑' m : ℕ, actualMomentTerm n r (m + 2 * n)) ≤
      tailCoefficient n r / (2 * (n : ℝ)) ^ tailPower n r * (9 / 7 : ℝ) := by
  have hs : 2 ≤ tailPower n r := by have := tailPower_ge n r hr; omega
  have hmajor : Summable (fun m : ℕ =>
      tailCoefficient n r / ((m + 2 * n : ℕ) : ℝ) ^ tailPower n r) := by
    simpa only [mul_one_div] using
      (AnalyticPSeriesTail.reciprocal_power_tail_summable (2 * n) (tailPower n r) hs).mul_left
        (tailCoefficient n r)
  have hminor : Summable (fun m : ℕ => actualMomentTerm n r (m + 2 * n)) := by
    apply Summable.of_nonneg_of_le _ _ hmajor
    · intro m
      exact actualMomentTerm_nonneg n r (m + 2 * n) (by omega)
    · intro m
      exact actual_tail_momentTerm_bound n r (m + 2 * n) hn hr (by omega)
  have hterm : (∑' m : ℕ, actualMomentTerm n r (m + 2 * n)) ≤
      ∑' m : ℕ, tailCoefficient n r / ((m + 2 * n : ℕ) : ℝ) ^ tailPower n r :=
    Summable.tsum_le_tsum
      (fun m => actual_tail_momentTerm_bound n r (m + 2 * n) hn hr (by omega)) hminor hmajor
  have hp := AnalyticPSeriesTail.reciprocal_power_tail_bound_factored
    (2 * n) (tailPower n r) (by omega) hs
  have hs1 : (0 : ℝ) < ((tailPower n r - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < tailPower n r - 1 by omega)
  have hden : 7 * (n : ℝ) ≤ ((tailPower n r - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 7 * n ≤ tailPower n r - 1 by have := tailPower_ge n r hr; omega)
  have hratio : 1 + (2 * n : ℝ) / ((tailPower n r - 1 : ℕ) : ℝ) ≤ (9 / 7 : ℝ) := by
    have h := (div_le_iff₀ hs1).mpr (by nlinarith :
      (2 * n : ℝ) ≤ (2 / 7 : ℝ) * ((tailPower n r - 1 : ℕ) : ℝ))
    linarith
  have hratio_nat :
      1 + ((2 * n : ℕ) : ℝ) / ((tailPower n r - 1 : ℕ) : ℝ) ≤ (9 / 7 : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hratio
  calc
    (∑' m : ℕ, actualMomentTerm n r (m + 2 * n)) ≤
        ∑' m : ℕ, tailCoefficient n r / ((m + 2 * n : ℕ) : ℝ) ^ tailPower n r := hterm
    _ = tailCoefficient n r * (∑' m : ℕ, 1 / ((m + 2 * n : ℕ) : ℝ) ^ tailPower n r) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      rw [mul_one_div]
    _ ≤ tailCoefficient n r *
        (1 / ((2 * n : ℕ) : ℝ) ^ tailPower n r *
          (1 + ((2 * n : ℕ) : ℝ) / ((tailPower n r - 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hp (tailCoefficient_nonneg n r)
    _ ≤ tailCoefficient n r *
        (1 / ((2 * n : ℕ) : ℝ) ^ tailPower n r * (9 / 7 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (tailCoefficient_nonneg n r)
      exact mul_le_mul_of_nonneg_left hratio_nat (by positivity)
    _ = _ := by push_cast; ring

theorem actualMoment_eq_compact_add_tail (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    actualMoment n r = (∑ m ∈ range (2 * n - 1), actualMomentSequence n r m) +
      ∑' m : ℕ, actualMomentTerm n r (m + 2 * n) := by
  have h := (actualMomentSequence_summable n r hn hr).sum_add_tsum_nat_add (2 * n - 1)
  have hindex : ∀ m : ℕ, m + (2 * n - 1) + 1 = m + 2 * n := by intro m; omega
  simpa only [actualMoment, actualMomentSequence, hindex] using h.symm

theorem actualMoment_compact_add_factorial_tail_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    actualMoment n r ≤
      5184 * Real.exp 18 * (n : ℝ) ^ 10 * (n : ℝ) ^ (2 * r) *
        Real.exp (-(2641 / 250 : ℝ) * n) +
      tailCoefficient n r / (2 * (n : ℝ)) ^ tailPower n r * (9 / 7 : ℝ) := by
  rw [actualMoment_eq_compact_add_tail n r hn hr]
  exact add_le_add (actual_compact_moment_sum_bound n r hn hr)
    (actual_tail_moment_sum_factorial_bound n r hn hr)

end ZetaNine.AnalyticMomentBounds

#print axioms ZetaNine.AnalyticMomentBounds.actualR_zero_of_pos_le
#print axioms ZetaNine.AnalyticMomentBounds.actualMomentSequence_summable
#print axioms ZetaNine.AnalyticMomentBounds.actualMomentSequence_norm_summable
#print axioms ZetaNine.AnalyticMomentBounds.actual_compact_moment_sum_bound
#print axioms ZetaNine.AnalyticMomentBounds.actual_tail_moment_sum_factorial_bound
#print axioms ZetaNine.AnalyticMomentBounds.actualMoment_eq_compact_add_tail
#print axioms ZetaNine.AnalyticMomentBounds.actualMoment_compact_add_factorial_tail_bound


/- SOURCE module: AnalyticUniformMomentBound; complete theorem bodies retained. -/

/-!
UNCOMPILED SOURCE preparation. This connects the actual compact sum and
infinite factorial-tail bound to a coefficient-independent five-moment
exponential bound. Every estimate is proved from n >= 1 and r <= 4.
Changing-coefficient polynomial evaluation and uniform-o(1) endpoints remain
to be added before the full weighted Z9.A statement can be claimed.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section
open scoped BigOperators

namespace ZetaNine.AnalyticUniformMomentBound
open AnalyticMomentBounds









theorem tailWeightConstant_pos (r : ℕ) : 0 < tailWeightConstant r := by
  unfold tailWeightConstant
  positivity

theorem tailWeightConstant_le (r : ℕ) (hr : r ≤ 4) :
    tailWeightConstant r ≤ (729 / 224 : ℝ) := by
  unfold tailWeightConstant
  interval_cases r <;> norm_num

theorem tailMajorant_pos (n r : ℕ) (hn : 1 ≤ n) : 0 < tailMajorant n r := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hfact := AnalyticFactorialBounds.real_factorial_pos n
  unfold tailMajorant tailCoefficient
  positivity

theorem log_tailWeightConstant (r : ℕ) :
    Real.log (tailWeightConstant r) = Real.log (9 / 7 : ℝ) +
      (r : ℝ) * Real.log (3 / 2 : ℝ) -
      ((9 - 2 * r : ℕ) : ℝ) * Real.log 2 := by
  unfold tailWeightConstant
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by norm_num : (9 / 7 : ℝ) ≠ 0) (by positivity),
    Real.log_pow, Real.log_pow]

theorem log_tailMajorant_identity (n r : ℕ) (hn : 1 ≤ n) :
    Real.log (tailMajorant n r) =
      7 * Real.log (n.factorial : ℝ) + (n : ℝ) * Real.log 2 +
      (r : ℝ) * Real.log (3 / 2 : ℝ) -
      (tailPower n r : ℝ) * (Real.log 2 + Real.log (n : ℝ)) +
      Real.log (9 / 7 : ℝ) - ((2 * r : ℕ) : ℝ) * Real.log (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hfact := AnalyticFactorialBounds.real_factorial_pos n
  unfold tailMajorant tailCoefficient
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by norm_num : (9 / 7 : ℝ) ≠ 0),
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0.ne']
  norm_num

theorem log_tailMajorant_upper (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    Real.log (tailMajorant n r) ≤ Real.log (tailWeightConstant r) + 7 -
      tailExponent * n - 2 * Real.log (n : ℝ) := by
  have hfact := AnalyticFactorialBounds.log_factorial_upper n hn
  have hidentity := log_tailMajorant_identity n r hn
  have hconstant := log_tailWeightConstant r
  have hsdom : 2 * r ≤ 7 * n + 9 := by omega
  have hrdomain : 2 * r ≤ 9 := by omega
  have hscast : (tailPower n r : ℝ) = 7 * (n : ℝ) + 9 - 2 * (r : ℝ) := by
    unfold tailPower
    rw [Nat.cast_sub hsdom]
    push_cast
    ring
  have hrcast : ((9 - 2 * r : ℕ) : ℝ) = 9 - 2 * (r : ℝ) := by
    rw [Nat.cast_sub hrdomain]
    push_cast
    ring
  rw [hscast] at hidentity
  rw [hrcast] at hconstant
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hidentity
  unfold tailExponent
  nlinarith

theorem certified_tailExponent_gap :
    (2641 / 250 : ℝ) + (297441 / 500000 : ℝ) < tailExponent := by
  have h := AnalyticPhase.log_two_lower_rational
  unfold tailExponent
  nlinarith

theorem tailMajorant_certified_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    tailMajorant n r ≤ (729 / 224 : ℝ) * Real.exp 7 *
      Real.exp (-(2641 / 250 : ℝ) * n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hconstant := Real.log_le_log (tailWeightConstant_pos r) (tailWeightConstant_le r hr)
  have hgamma : (2641 / 250 : ℝ) ≤ tailExponent := by have := certified_tailExponent_gap; linarith
  have hmul := mul_le_mul_of_nonneg_right hgamma hn0.le
  have hlog : Real.log (tailMajorant n r) ≤
      Real.log (729 / 224 : ℝ) + 7 - (2641 / 250 : ℝ) * n := by
    have h := log_tailMajorant_upper n r hn hr
    nlinarith
  have h := (Real.log_le_iff_le_exp (tailMajorant_pos n r hn)).mp hlog
  have he : Real.exp (Real.log (729 / 224 : ℝ) + 7 - (2641 / 250 : ℝ) * n) =
      (729 / 224 : ℝ) * Real.exp 7 * Real.exp (-(2641 / 250 : ℝ) * n) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_add,
      Real.exp_log (by norm_num : (0 : ℝ) < 729 / 224)]
    rw [neg_mul]
  exact h.trans_eq he

theorem actual_tail_moment_sum_certified_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    (∑' m : ℕ, actualMomentTerm n r (m + 2 * n)) ≤
      (729 / 224 : ℝ) * Real.exp 7 * Real.exp (-(2641 / 250 : ℝ) * n) *
        (n : ℝ) ^ (2 * r) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpow : (0 : ℝ) < (n : ℝ) ^ (2 * r) := pow_pos hn0 _
  have h := div_le_div_of_nonneg_right
    (actual_tail_moment_sum_factorial_bound n r hn hr) hpow.le
  have hnormal : (∑' m : ℕ, actualMomentTerm n r (m + 2 * n)) / (n : ℝ) ^ (2 * r) ≤
      tailMajorant n r := h
  exact (div_le_iff₀ hpow).mp (hnormal.trans (tailMajorant_certified_bound n r hn hr))

theorem momentBoundConstant_pos : 0 < momentBoundConstant := by
  unfold momentBoundConstant
  positivity

/-- The actual raw five moments, including all first n zero terms. -/
theorem actualMoment_uniform_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    actualMoment n r ≤ momentBoundConstant * ((n : ℝ) + 1) ^ 10 *
      Real.exp (-(2641 / 250 : ℝ) * n) * (n : ℝ) ^ (2 * r) := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hpow0 : (n : ℝ) ^ 10 ≤ ((n : ℝ) + 1) ^ 10 :=
    pow_le_pow_left₀ hn0 (by linarith) _
  have hpow1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 10 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hn1 10
  have hcomp := actual_compact_moment_sum_bound n r hn hr
  have htail := actual_tail_moment_sum_certified_bound n r hn hr
  have hsplit := actualMoment_eq_compact_add_tail n r hn hr
  have hsum : actualMoment n r ≤
      (5184 * Real.exp 18 * (n : ℝ) ^ 10 + (729 / 224 : ℝ) * Real.exp 7) *
        (Real.exp (-(2641 / 250 : ℝ) * n) * (n : ℝ) ^ (2 * r)) := by
    rw [hsplit]
    have h := add_le_add hcomp htail
    convert h using 1 <;> first | rfl | ring
  have hc0 : (0 : ℝ) ≤ 5184 * Real.exp 18 := by positivity
  have hc1 : (0 : ℝ) ≤ (729 / 224 : ℝ) * Real.exp 7 := by positivity
  have hcoef : 5184 * Real.exp 18 * (n : ℝ) ^ 10 + (729 / 224 : ℝ) * Real.exp 7 ≤
      momentBoundConstant * ((n : ℝ) + 1) ^ 10 := by
    have h0 := mul_le_mul_of_nonneg_left hpow0 hc0
    have h1 := mul_le_mul_of_nonneg_left hpow1 hc1
    unfold momentBoundConstant
    nlinarith
  exact hsum.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoef (by positivity))

end ZetaNine.AnalyticUniformMomentBound

#print axioms ZetaNine.AnalyticUniformMomentBound.log_tailMajorant_upper
#print axioms ZetaNine.AnalyticUniformMomentBound.certified_tailExponent_gap
#print axioms ZetaNine.AnalyticUniformMomentBound.tailMajorant_certified_bound
#print axioms ZetaNine.AnalyticUniformMomentBound.actual_tail_moment_sum_certified_bound
#print axioms ZetaNine.AnalyticUniformMomentBound.actualMoment_uniform_bound


/- SOURCE module: AnalyticWeightedBound; complete theorem bodies retained. -/

/-!
UNCOMPILED SOURCE preparation for the actual weighted Z9.A upper bound.
The raw series is definitionally the original rational weightedR at m+1.
No coefficient growth, parity, HasSum, moment bound, or uniform error bound
is an input hypothesis. The only domains are n >= 1 and natDegree W <= 4.

This SOURCE includes the actual arbitrary-quartic triangle bound and an
explicit coefficient-independent error tending to zero. It becomes a
formalized result only after actual author and independent kernel checks.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section
open scoped BigOperators Topology
open Finset Filter Polynomial

namespace ZetaNine.AnalyticWeightedBound
open AnalyticMomentBounds AnalyticUniformMomentBound









theorem actualWeightedSequence_eq_actual_moment_sum (n : ℕ) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) (m : ℕ) :
    actualWeightedSequence n W m =
      ∑ r ∈ range 5, (W.coeff r : ℝ) * actualMomentSequence n r m := by
  unfold actualWeightedSequence CoefficientMap.weightedR
  rw [Polynomial.eval_eq_sum_range' (by omega : W.natDegree < 5)]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  unfold actualMomentSequence actualMomentTerm
  push_cast
  ring

theorem actualWeighted_hasSum_actual_moments (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    HasSum (actualWeightedSequence n W)
      (∑ r ∈ range 5, (W.coeff r : ℝ) * actualMoment n r) := by
  have hsum : HasSum
      (fun m : ℕ => ∑ r ∈ range 5, (W.coeff r : ℝ) * actualMomentSequence n r m)
      (∑ r ∈ range 5, (W.coeff r : ℝ) * actualMoment n r) := by
    apply hasSum_sum
    intro r hr
    have hr4 : r ≤ 4 := by have := mem_range.mp hr; omega
    exact (actualMomentSequence_summable n r hn hr4).hasSum.mul_left (W.coeff r : ℝ)
  exact hsum.congr_fun (fun m => actualWeightedSequence_eq_actual_moment_sum n W hW m)

theorem actualWeighted_summable (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    Summable (actualWeightedSequence n W) :=
  (actualWeighted_hasSum_actual_moments n hn W hW).summable

theorem actualWeighted_norm_summable (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    Summable (fun m : ℕ => ‖actualWeightedSequence n W m‖) :=
  (actualWeighted_summable n hn W hW).norm

theorem actualWeighted_tsum_eq_actual_moment_sum (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    (∑' m : ℕ, actualWeightedSequence n W m) =
      ∑ r ∈ range 5, (W.coeff r : ℝ) * actualMoment n r :=
  (actualWeighted_hasSum_actual_moments n hn W hW).tsum_eq

theorem actualMoment_nonneg (n r : ℕ) : 0 ≤ actualMoment n r := by
  unfold actualMoment
  exact tsum_nonneg (actualMomentSequence_nonneg n r)

theorem weightedCoefficientHeight_nonneg (n : ℕ) (W : ℚ[X]) :
    0 ≤ weightedCoefficientHeight n W := by
  unfold weightedCoefficientHeight
  apply Finset.sum_nonneg
  intro r hr
  positivity

theorem actualWeighted_uniform_bound (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    |∑' m : ℕ, actualWeightedSequence n W m| ≤
      analyticPrefactor n * weightedCoefficientHeight n W := by
  rw [actualWeighted_tsum_eq_actual_moment_sum n hn W hW]
  calc
    |∑ r ∈ range 5, (W.coeff r : ℝ) * actualMoment n r| ≤
        ∑ r ∈ range 5, |(W.coeff r : ℝ) * actualMoment n r| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ r ∈ range 5, |(W.coeff r : ℝ)| * actualMoment n r := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [abs_mul, abs_of_nonneg (actualMoment_nonneg n r)]
    _ ≤ ∑ r ∈ range 5, |(W.coeff r : ℝ)| *
        (analyticPrefactor n * (n : ℝ) ^ (2 * r)) := by
      apply Finset.sum_le_sum
      intro r hr
      have hr4 : r ≤ 4 := by have := mem_range.mp hr; omega
      exact mul_le_mul_of_nonneg_left (actualMoment_uniform_bound n r hn hr4) (abs_nonneg _)
    _ = analyticPrefactor n * weightedCoefficientHeight n W := by
      unfold weightedCoefficientHeight
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring

/-- The bound holds pointwise for any family; its prefactor has no family input. -/
theorem changing_quartics_uniform_bound (W : ℕ → ℚ[X])
    (hW : ∀ n : ℕ, (W n).natDegree ≤ 4) :
    ∀ n : ℕ, 1 ≤ n → |∑' m : ℕ, actualWeightedSequence n (W n) m| ≤
      analyticPrefactor n * weightedCoefficientHeight n (W n) := by
  intro n hn
  exact actualWeighted_uniform_bound n hn (W n) (hW n)

theorem uniformError_tendsto_zero : Tendsto uniformError atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hplus : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 hnat
  have hlog := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hplus
  have hlog' : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 0) := by
    convert hlog using 1
    funext n
    simp only [Function.comp_apply, pow_one, one_mul]
    congr 2 <;> ring
  have hconst : Tendsto (fun n : ℕ => Real.log momentBoundConstant / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have h := hconst.add (hlog'.const_mul 10)
  convert h using 1
  · funext n
    unfold uniformError
    rw [add_div]
    ring
  · norm_num

theorem analyticPrefactor_eq_uniform_exponent (n : ℕ) (hn : 1 ≤ n) :
    analyticPrefactor n = Real.exp ((-(2641 / 250 : ℝ) + uniformError n) * n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have he : (-(2641 / 250 : ℝ) + uniformError n) * n =
      -(2641 / 250 : ℝ) * n + Real.log momentBoundConstant +
        10 * Real.log ((n : ℝ) + 1) := by
    unfold uniformError
    field_simp [hn0.ne']
    ring
  rw [he]
  rw [show 10 * Real.log ((n : ℝ) + 1) = Real.log (((n : ℝ) + 1) ^ 10) by
    simpa only [Nat.cast_ofNat] using (Real.log_pow ((n : ℝ) + 1) 10).symm]
  unfold analyticPrefactor
  rw [Real.exp_add, Real.exp_add, Real.exp_log momentBoundConstant_pos,
    Real.exp_log (pow_pos hnp 10)]
  ring

/-- Actual weighted route A: an explicit error independent of all quartic coefficients. -/
theorem actual_weighted_uniform_o_one :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ W : ℚ[X], W.natDegree ≤ 4 →
        |∑' m : ℕ, actualWeightedSequence n W m| ≤
          Real.exp ((-(2641 / 250 : ℝ) + ε n) * n) * weightedCoefficientHeight n W := by
  refine ⟨uniformError, uniformError_tendsto_zero, ?_⟩
  intro n hn W hW
  rw [← analyticPrefactor_eq_uniform_exponent n hn]
  exact actualWeighted_uniform_bound n hn W hW

end ZetaNine.AnalyticWeightedBound

#print axioms ZetaNine.AnalyticWeightedBound.actualWeightedSequence_eq_actual_moment_sum
#print axioms ZetaNine.AnalyticWeightedBound.actualWeighted_hasSum_actual_moments
#print axioms ZetaNine.AnalyticWeightedBound.actualWeighted_norm_summable
#print axioms ZetaNine.AnalyticWeightedBound.actualWeighted_uniform_bound
#print axioms ZetaNine.AnalyticWeightedBound.changing_quartics_uniform_bound
#print axioms ZetaNine.AnalyticWeightedBound.uniformError_tendsto_zero
#print axioms ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 200000
noncomputable section
open scoped BigOperators Topology
open Set Finset Filter Polynomial
open ZetaNine
open ZetaNine.AnalyticMomentBounds ZetaNine.AnalyticUniformMomentBound
open ZetaNine.AnalyticWeightedBound

theorem solution :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ W : ℚ[X], W.natDegree ≤ 4 →
        |∑' m : ℕ, actualWeightedSequence n W m| ≤
          Real.exp ((-(2641 / 250 : ℝ) + ε n) * n) * weightedCoefficientHeight n W := by
  exact @ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one

#print axioms solution

-- Prove2me | solution 1 for PiIrrationality.Bai.coef_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T20:09:12.372914+00:00
-- url     : https://prove2.me/submissions/5353f224-4bb8-4754-801e-e31ea8f37f3f

import Definitions.Def_PiIrrationality_BaiForms
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic
set_option autoImplicit false

namespace BaiCert
open Polynomial

/-- Partial sum `∑_{k<N} 2 y^(2k+1)/(2k+1)` of the series of `log (1+y) - log (1-y)`. -/
noncomputable def atanhPS (y : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * y ^ (2 * k + 1)

lemma atanh_tail (y : ℝ) (hy : |y| < 1) (N : ℕ) :
    |Real.log (1 + y) - Real.log (1 - y) - atanhPS y N| ≤
      2 * |y| ^ (2 * N + 1) / ((2 * (N : ℝ) + 1) * (1 - |y| ^ 2)) := by
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one hy
  have h1 := hs.summable.sum_add_tsum_nat_add N
  rw [hs.tsum_eq] at h1
  have h2 : Real.log (1 + y) - Real.log (1 - y) - atanhPS y N =
      ∑' i : ℕ, (2 : ℝ) * (1 / (2 * ((i + N : ℕ) : ℝ) + 1)) * y ^ (2 * (i + N) + 1) := by
    unfold atanhPS; rw [← h1]; ring
  rw [h2]
  have ha : 0 ≤ |y| := abs_nonneg y
  have ha2 : |y| ^ 2 < 1 := by nlinarith
  have hN : (0 : ℝ) < 2 * (N : ℝ) + 1 := by positivity
  set C : ℝ := 2 * |y| ^ (2 * N + 1) / (2 * (N : ℝ) + 1) with hC
  have hbound : ∀ i : ℕ, ‖(2 : ℝ) * (1 / (2 * ((i + N : ℕ) : ℝ) + 1)) * y ^ (2 * (i + N) + 1)‖ ≤
      C * (|y| ^ 2) ^ i := by
    intro i
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
    have e1 : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
    have e2 : |1 / (2 * ((i + N : ℕ) : ℝ) + 1)| = 1 / (2 * ((i + N : ℕ) : ℝ) + 1) :=
      abs_of_pos (by positivity)
    rw [e1, e2]
    have e3 : |y| ^ (2 * (i + N) + 1) = |y| ^ (2 * N + 1) * (|y| ^ 2) ^ i := by
      rw [← pow_mul, ← pow_add]; congr 1; ring
    rw [e3, hC]
    have e4 : 1 / (2 * ((i + N : ℕ) : ℝ) + 1) ≤ 1 / (2 * (N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le hN
      push_cast; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    have e5 : 0 ≤ |y| ^ (2 * N + 1) * (|y| ^ 2) ^ i := by positivity
    calc (2 : ℝ) * (1 / (2 * ((i + N : ℕ) : ℝ) + 1)) * (|y| ^ (2 * N + 1) * (|y| ^ 2) ^ i)
        ≤ 2 * (1 / (2 * (N : ℝ) + 1)) * (|y| ^ (2 * N + 1) * (|y| ^ 2) ^ i) := by
          gcongr
      _ = 2 * |y| ^ (2 * N + 1) / (2 * (N : ℝ) + 1) * (|y| ^ 2) ^ i := by ring
  have hgeo : Summable (fun i : ℕ => C * (|y| ^ 2) ^ i) :=
    (summable_geometric_of_lt_one (by positivity) ha2).mul_left C
  have hsum : Summable (fun i : ℕ =>
      ‖(2 : ℝ) * (1 / (2 * ((i + N : ℕ) : ℝ) + 1)) * y ^ (2 * (i + N) + 1)‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hbound hgeo
  calc |∑' i : ℕ, (2 : ℝ) * (1 / (2 * ((i + N : ℕ) : ℝ) + 1)) * y ^ (2 * (i + N) + 1)|
      = ‖∑' i : ℕ, (2 : ℝ) * (1 / (2 * ((i + N : ℕ) : ℝ) + 1)) * y ^ (2 * (i + N) + 1)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∑' i : ℕ, ‖(2 : ℝ) * (1 / (2 * ((i + N : ℕ) : ℝ) + 1)) * y ^ (2 * (i + N) + 1)‖ :=
        norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' i : ℕ, C * (|y| ^ 2) ^ i := hsum.tsum_le_tsum hbound hgeo
    _ = C * (1 - |y| ^ 2)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) ha2]
    _ = 2 * |y| ^ (2 * N + 1) / ((2 * (N : ℝ) + 1) * (1 - |y| ^ 2)) := by
        rw [hC]; field_simp


lemma log_approx (q : ℝ) (hq : 0 < q) (N : ℕ) :
    |Real.log q - atanhPS ((q - 1) / (q + 1)) N| ≤
      2 * |(q - 1) / (q + 1)| ^ (2 * N + 1) /
        ((2 * (N : ℝ) + 1) * (1 - |(q - 1) / (q + 1)| ^ 2)) := by
  have hq1 : 0 < q + 1 := by linarith
  have hy : |(q - 1) / (q + 1)| < 1 := by
    rw [abs_lt]
    constructor
    · rw [lt_div_iff₀ hq1]; linarith
    · rw [div_lt_iff₀ hq1]; linarith
  have h := atanh_tail _ hy N
  have hl : Real.log (1 + (q - 1) / (q + 1)) - Real.log (1 - (q - 1) / (q + 1)) = Real.log q := by
    have h1 : (1 + (q - 1) / (q + 1)) ≠ 0 := by
      have : 1 + (q - 1) / (q + 1) = 2 * q / (q + 1) := by field_simp; ring
      rw [this]; positivity
    have h2 : (1 - (q - 1) / (q + 1)) ≠ 0 := by
      have : 1 - (q - 1) / (q + 1) = 2 / (q + 1) := by field_simp; ring
      rw [this]; positivity
    rw [← Real.log_div h1 h2]
    congr 1
    field_simp
    ring
  rw [hl] at h
  exact h

lemma log_bound_mono (a Y : ℝ) (N : ℕ) (ha : 0 ≤ a) (haY : a ≤ Y) (hY : Y < 1) :
    2 * a ^ (2 * N + 1) / ((2 * (N : ℝ) + 1) * (1 - a ^ 2)) ≤
      2 * Y ^ (2 * N + 1) / ((2 * (N : ℝ) + 1) * (1 - Y ^ 2)) := by
  have hN : (0 : ℝ) < 2 * (N : ℝ) + 1 := by positivity
  have hY0 : 0 ≤ Y := ha.trans haY
  have hY2 : Y ^ 2 < 1 := by nlinarith
  have hd : 0 < (2 * (N : ℝ) + 1) * (1 - Y ^ 2) := mul_pos hN (by linarith)
  apply div_le_div₀ (by positivity) _ hd
  · apply mul_le_mul_of_nonneg_left _ hN.le
    nlinarith
  · have : a ^ (2 * N + 1) ≤ Y ^ (2 * N + 1) := pow_le_pow_left₀ ha haY _
    linarith

lemma log_le_of (q y Y L : ℝ) (N : ℕ) (hq : 0 < q) (hy : y = (q - 1) / (q + 1)) (hY : |y| ≤ Y)
    (hY1 : Y < 1)
    (hL : atanhPS y N + 2 * Y ^ (2 * N + 1) / ((2 * (N : ℝ) + 1) * (1 - Y ^ 2)) ≤ L) :
    Real.log q ≤ L := by
  subst hy
  have h := (abs_le.1 (log_approx q hq N)).2
  have hb := log_bound_mono _ Y N (abs_nonneg _) hY hY1
  linarith

lemma le_log_of (q y Y L : ℝ) (N : ℕ) (hq : 0 < q) (hy : y = (q - 1) / (q + 1)) (hY : |y| ≤ Y)
    (hY1 : Y < 1)
    (hL : L ≤ atanhPS y N - 2 * Y ^ (2 * N + 1) / ((2 * (N : ℝ) + 1) * (1 - Y ^ 2))) :
    L ≤ Real.log q := by
  subst hy
  have h := (abs_le.1 (log_approx q hq N)).1
  have hb := log_bound_mono _ Y N (abs_nonneg _) hY hY1
  linarith


lemma log_two_bounds : (0.69314718055994530941723212 : ℝ) ≤ Real.log (2 : ℝ) ∧ Real.log (2 : ℝ) ≤ (0.69314718055994530941723213 : ℝ) := by
  constructor
  · exact le_log_of (2 : ℝ) (1 / 3 : ℝ) (166667 / 500000 : ℝ) _ 30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])
  · exact log_le_of (2 : ℝ) (1 / 3 : ℝ) (166667 / 500000 : ℝ) _ 30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])

lemma log_qa_bounds : (0.21445259536239059556441382 : ℝ) ≤ Real.log (1330563019 / 1073741824 : ℝ) ∧ Real.log (1330563019 / 1073741824 : ℝ) ≤ (0.21445259536239059556441391 : ℝ) := by
  constructor
  · exact le_log_of (1330563019 / 1073741824 : ℝ) (256821195 / 2404304843 : ℝ) (53409 / 500000 : ℝ) _ 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])
  · exact log_le_of (1330563019 / 1073741824 : ℝ) (256821195 / 2404304843 : ℝ) (53409 / 500000 : ℝ) _ 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])

lemma log_qb_bounds : (0.00960975754181462829298287 : ℝ) ≤ Real.log (2684126254035284887019056953716885041 / 2658455991569831745807614120560689152 : ℝ) ∧ Real.log (2684126254035284887019056953716885041 / 2658455991569831745807614120560689152 : ℝ) ≤ (0.00960975754181462829298288 : ℝ) := by
  constructor
  · exact le_log_of (2684126254035284887019056953716885041 / 2658455991569831745807614120560689152 : ℝ) (25670262465453141211442833156195889 / 5342582245605116632826671074277574193 : ℝ) (961 / 200000 : ℝ) _ 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])
  · exact log_le_of (2684126254035284887019056953716885041 / 2658455991569831745807614120560689152 : ℝ) (25670262465453141211442833156195889 / 5342582245605116632826671074277574193 : ℝ) (961 / 200000 : ℝ) _ 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])

lemma log_qc_bounds : (-0.27336291802018918363782469 : ℝ) ≤ Real.log (816920629 / 1073741824 : ℝ) ∧ Real.log (816920629 / 1073741824 : ℝ) ≤ (-0.27336291802018918363782467 : ℝ) := by
  constructor
  · exact le_log_of (816920629 / 1073741824 : ℝ) (-256821195 / 1890662453 : ℝ) (135837 / 1000000 : ℝ) _ 14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])
  · exact log_le_of (816920629 / 1073741824 : ℝ) (-256821195 / 1890662453 : ℝ) (135837 / 1000000 : ℝ) _ 14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])

lemma log_qd_bounds : (-0.04423039425748904904241733 : ℝ) ≤ Real.log (256821195 / 268435456 : ℝ) ∧ Real.log (256821195 / 268435456 : ℝ) ≤ (-0.04423039425748904904241732 : ℝ) := by
  constructor
  · exact le_log_of (256821195 / 268435456 : ℝ) (-11614261 / 525256651 : ℝ) (691 / 31250 : ℝ) _ 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])
  · exact log_le_of (256821195 / 268435456 : ℝ) (-11614261 / 525256651 : ℝ) (691 / 31250 : ℝ) _ 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])

/-! ## Generating-function bound for `(1-x)^{-(e+1)}` -/

lemma S_identity (x : ℝ) (e M : ℕ) :
    (1 - x) * (∑ m ∈ Finset.range (M + 1), ((Nat.choose (e + 1 + m) m : ℕ) : ℝ) * x ^ m) +
      ((Nat.choose (e + 1 + M) M : ℕ) : ℝ) * x ^ (M + 1) =
    ∑ m ∈ Finset.range (M + 1), ((Nat.choose (e + m) m : ℕ) : ℝ) * x ^ m := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ (fun m => ((Nat.choose (e + 1 + m) m : ℕ) : ℝ) * x ^ m) (M + 1),
      Finset.sum_range_succ (fun m => ((Nat.choose (e + m) m : ℕ) : ℝ) * x ^ m) (M + 1)]
    have pascal : ((Nat.choose (e + 1 + (M + 1)) (M + 1) : ℕ) : ℝ) =
        ((Nat.choose (e + 1 + M) M : ℕ) : ℝ) + ((Nat.choose (e + (M + 1)) (M + 1) : ℕ) : ℝ) := by
      have h1 : e + 1 + (M + 1) = (e + 1 + M) + 1 := by omega
      have h2 : e + (M + 1) = e + 1 + M := by omega
      rw [h1, Nat.choose_succ_succ', h2]
      push_cast; ring
    linear_combination ih + x ^ (M + 1) * pascal

lemma S_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (e M : ℕ) :
    (1 - x) ^ (e + 1) * ∑ m ∈ Finset.range (M + 1), ((Nat.choose (e + m) m : ℕ) : ℝ) * x ^ m ≤ 1 := by
  induction e with
  | zero =>
    simp only [zero_add, Nat.choose_self, Nat.cast_one, one_mul, pow_one]
    have h := geom_sum_mul_neg x (M + 1)
    have : 0 ≤ x ^ (M + 1) := pow_nonneg hx0 _
    rw [mul_comm]; linarith
  | succ e ih =>
    have h1 := S_identity x e M
    have h2 : 0 ≤ ((Nat.choose (e + 1 + M) M : ℕ) : ℝ) * x ^ (M + 1) := by positivity
    have h3 : (1 - x) * (∑ m ∈ Finset.range (M + 1), ((Nat.choose (e + 1 + m) m : ℕ) : ℝ) * x ^ m)
        ≤ ∑ m ∈ Finset.range (M + 1), ((Nat.choose (e + m) m : ℕ) : ℝ) * x ^ m := by linarith
    have h4 : 0 ≤ (1 - x) ^ (e + 1) := pow_nonneg (by linarith) _
    calc (1 - x) ^ (e + 1 + 1) *
          ∑ m ∈ Finset.range (M + 1), ((Nat.choose (e + 1 + m) m : ℕ) : ℝ) * x ^ m
        = (1 - x) ^ (e + 1) * ((1 - x) *
          ∑ m ∈ Finset.range (M + 1), ((Nat.choose (e + 1 + m) m : ℕ) : ℝ) * x ^ m) := by ring
      _ ≤ (1 - x) ^ (e + 1) * ∑ m ∈ Finset.range (M + 1), ((Nat.choose (e + m) m : ℕ) : ℝ) * x ^ m :=
          mul_le_mul_of_nonneg_left h3 h4
      _ ≤ 1 := ih

lemma term_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (e m : ℕ) :
    ((Nat.choose (e + m) m : ℕ) : ℝ) * x ^ m * (1 - x) ^ (e + 1) ≤ 1 := by
  have h := S_le x hx0 hx1 e m
  have hle : ((Nat.choose (e + m) m : ℕ) : ℝ) * x ^ m ≤
      ∑ j ∈ Finset.range (m + 1), ((Nat.choose (e + j) j : ℕ) : ℝ) * x ^ j :=
    Finset.single_le_sum (f := fun j => ((Nat.choose (e + j) j : ℕ) : ℝ) * x ^ j)
      (fun j _ => by positivity) (Finset.mem_range.2 (Nat.lt_succ_self m))
  have h4 : 0 ≤ (1 - x) ^ (e + 1) := pow_nonneg (by linarith) _
  calc ((Nat.choose (e + m) m : ℕ) : ℝ) * x ^ m * (1 - x) ^ (e + 1)
      ≤ (∑ j ∈ Finset.range (m + 1), ((Nat.choose (e + j) j : ℕ) : ℝ) * x ^ j) * (1 - x) ^ (e + 1) :=
        mul_le_mul_of_nonneg_right hle h4
    _ = (1 - x) ^ (e + 1) * ∑ j ∈ Finset.range (m + 1), ((Nat.choose (e + j) j : ℕ) : ℝ) * x ^ j := by
        ring
    _ ≤ 1 := h

/-- a partial sum of a polynomial with natural coefficients, evaluated at `x ≥ 0`, is at most the value -/
lemma partial_le_aeval (p : ℕ[X]) (x : ℝ) (hx : 0 ≤ x) (M : ℕ) :
    ∑ k ∈ Finset.range M, (p.coeff k : ℝ) * x ^ k ≤ Polynomial.aeval x p := by
  set M' := max M (p.natDegree + 1) with hM'
  have h1 : Polynomial.aeval x p = ∑ k ∈ Finset.range M', (p.coeff k : ℝ) * x ^ k := by
    rw [Polynomial.aeval_eq_sum_range' (n := M') (by omega)]
    simp [nsmul_eq_mul]
  rw [h1]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (le_max_left _ _)
  · intro k _ _; positivity

open Polynomial in
lemma coef_aux (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    (PiIrrationality.Bai.coef n : ℝ) * x ^ (5570 * n) * (1 - x) ^ (7430 * n) ≤
      ((1 + x) ^ 3714 * (2 + 6 * x + 9 * x ^ 2 + 6 * x ^ 3 + 2 * x ^ 4) ^ 3714) ^ n := by
  have hA : Polynomial.aeval x (PiIrrationality.Bai.A ^ n) =
      ((1 + x) ^ 3714 * (2 + 6 * x + 9 * x ^ 2 + 6 * x ^ 3 + 2 * x ^ 4) ^ 3714) ^ n := by
    have h1 : Polynomial.aeval x (1 + X : ℕ[X]) = 1 + x := by simp
    have h2 : Polynomial.aeval x (C 2 + C 6 * X + C 9 * X ^ 2 + C 6 * X ^ 3 + C 2 * X ^ 4 : ℕ[X]) =
        2 + 6 * x + 9 * x ^ 2 + 6 * x ^ 3 + 2 * x ^ 4 := by simp [map_ofNat]
    unfold PiIrrationality.Bai.A
    rw [map_pow, map_mul, map_pow, map_pow, h1, h2]
  rw [← hA]
  refine le_trans ?_ (partial_le_aeval _ x hx0.le (5570 * n + 1))
  unfold PiIrrationality.Bai.coef
  push_cast
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  have hk' : k ≤ 5570 * n := by have := Finset.mem_range.1 hk; omega
  have hd : 7430 * n = (7430 * n - 1) + 1 := by omega
  have key := term_le x hx0.le hx1 (7430 * n - 1) (5570 * n - k)
  have hxp : x ^ (5570 * n) = x ^ k * x ^ (5570 * n - k) := by
    rw [← pow_add]; congr 1; omega
  have hnn : 0 ≤ (((PiIrrationality.Bai.A ^ n).coeff k : ℕ) : ℝ) * x ^ k := by positivity
  calc (((PiIrrationality.Bai.A ^ n).coeff k : ℕ) : ℝ) *
        ((Nat.choose (7430 * n - 1 + (5570 * n - k)) (5570 * n - k) : ℕ) : ℝ) * x ^ (5570 * n) *
        (1 - x) ^ (7430 * n)
      = ((((PiIrrationality.Bai.A ^ n).coeff k : ℕ) : ℝ) * x ^ k) *
        (((Nat.choose (7430 * n - 1 + (5570 * n - k)) (5570 * n - k) : ℕ) : ℝ) *
          x ^ (5570 * n - k) * (1 - x) ^ (7430 * n - 1 + 1)) := by
        rw [hxp, ← hd]; ring
    _ ≤ ((((PiIrrationality.Bai.A ^ n).coeff k : ℕ) : ℝ) * x ^ k) * 1 :=
        mul_le_mul_of_nonneg_left key hnn
    _ = _ := mul_one _


noncomputable def xc : ℝ := 256821195 / 1073741824

lemma log_scale_div (q : ℝ) (hq : 0 < q) (k : ℕ) : Real.log (q / 2 ^ k) = Real.log q - k * Real.log 2 := by
  rw [Real.log_div hq.ne' (by positivity), Real.log_pow]

lemma sigma_log :
    3714 * Real.log (1 + xc) + 3714 * Real.log (2 + 6 * xc + 9 * xc ^ 2 + 6 * xc ^ 3 + 2 * xc ^ 4) - 7430 * Real.log (1 - xc) -
      5570 * Real.log xc ≤ 15979.97420422751 := by
  have ha := log_qa_bounds
  have hb := log_qb_bounds
  have hc := log_qc_bounds
  have hd := log_qd_bounds
  have h2 := log_two_bounds
  have e_a : 1 + xc = (1330563019 / 1073741824 : ℝ) := by norm_num [xc]
  have e_b : (2 + 6 * xc + 9 * xc ^ 2 + 6 * xc ^ 3 + 2 * xc ^ 4) / 2 ^ 2 = (2684126254035284887019056953716885041 / 2658455991569831745807614120560689152 : ℝ) := by norm_num [xc]
  have e_c : 1 - xc = (816920629 / 1073741824 : ℝ) := by norm_num [xc]
  have e_d : xc * 2 ^ 2 = (256821195 / 268435456 : ℝ) := by norm_num [xc]
  have hPpos : 0 < (2 + 6 * xc + 9 * xc ^ 2 + 6 * xc ^ 3 + 2 * xc ^ 4) := by norm_num [xc]
  have hxpos : 0 < xc := by norm_num [xc]
  have lb : Real.log (2 + 6 * xc + 9 * xc ^ 2 + 6 * xc ^ 3 + 2 * xc ^ 4) = Real.log ((2 + 6 * xc + 9 * xc ^ 2 + 6 * xc ^ 3 + 2 * xc ^ 4) / 2 ^ 2) + 2 * Real.log 2 := by
    have := log_scale_div (2 + 6 * xc + 9 * xc ^ 2 + 6 * xc ^ 3 + 2 * xc ^ 4) hPpos 2
    push_cast at this; linarith
  have ld : Real.log (xc * 2 ^ 2) = Real.log xc + 2 * Real.log 2 := by
    rw [Real.log_mul hxpos.ne' (by positivity), Real.log_pow]; push_cast; ring
  rw [e_a] at *
  rw [e_b] at lb
  rw [e_d] at ld
  rw [e_c]
  rw [e_a]
  linarith [ha.2, hb.2, hc.1, hd.1, h2.2]

lemma exp_step (c σ : ℝ) (n : ℕ) (hσ : 0 < σ) (h3 : Real.log σ ≤ c) :
    σ ^ n ≤ Real.exp (c * n) := by
  rw [← Real.exp_log hσ, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

lemma coef_le_aux (n : ℕ) :
    (PiIrrationality.Bai.coef n : ℝ) ≤ Real.exp (15979.97420422751 * (n : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [PiIrrationality.Bai.coef]
  have hx0 : 0 < xc := by norm_num [xc]
  have hx1 : xc < 1 := by norm_num [xc]
  have hpa : 0 < 1 + xc := by norm_num [xc]
  have hpb : 0 < (2 + 6 * xc + 9 * xc ^ 2 + 6 * xc ^ 3 + 2 * xc ^ 4) := by norm_num [xc]
  have h1xc : 0 < 1 - xc := by norm_num [xc]
  have h := coef_aux n hn xc hx0 hx1
  have hAvpos : 0 < (1 + xc) ^ 3714 * (2 + 6 * xc + 9 * xc ^ 2 + 6 * xc ^ 3 + 2 * xc ^ 4) ^ 3714 := mul_pos (pow_pos hpa _) (pow_pos hpb _)
  have hden : 0 < xc ^ 5570 * (1 - xc) ^ 7430 := mul_pos (pow_pos hx0 _) (pow_pos h1xc _)
  have hσ : 0 < (1 + xc) ^ 3714 * (2 + 6 * xc + 9 * xc ^ 2 + 6 * xc ^ 3 + 2 * xc ^ 4) ^ 3714 / (xc ^ 5570 * (1 - xc) ^ 7430) := div_pos hAvpos hden
  have h2 : (PiIrrationality.Bai.coef n : ℝ) ≤
      ((1 + xc) ^ 3714 * (2 + 6 * xc + 9 * xc ^ 2 + 6 * xc ^ 3 + 2 * xc ^ 4) ^ 3714 / (xc ^ 5570 * (1 - xc) ^ 7430)) ^ n := by
    rw [div_pow, mul_pow (xc ^ 5570), ← pow_mul, ← pow_mul, le_div_iff₀ (by positivity)]
    calc (PiIrrationality.Bai.coef n : ℝ) * (xc ^ (5570 * n) * (1 - xc) ^ (7430 * n))
        = (PiIrrationality.Bai.coef n : ℝ) * xc ^ (5570 * n) * (1 - xc) ^ (7430 * n) := by ring
      _ ≤ _ := h
  have l1 : Real.log ((1 + xc) ^ 3714 * (2 + 6 * xc + 9 * xc ^ 2 + 6 * xc ^ 3 + 2 * xc ^ 4) ^ 3714 / (xc ^ 5570 * (1 - xc) ^ 7430)) =
      (3714 * Real.log (1 + xc) + 3714 * Real.log (2 + 6 * xc + 9 * xc ^ 2 + 6 * xc ^ 3 + 2 * xc ^ 4)) -
        (5570 * Real.log xc + 7430 * Real.log (1 - xc)) := by
    rw [Real.log_div hAvpos.ne' hden.ne', Real.log_mul (pow_pos hpa _).ne' (pow_pos hpb _).ne',
      Real.log_mul (pow_pos hx0 _).ne' (pow_pos h1xc _).ne', Real.log_pow, Real.log_pow,
      Real.log_pow, Real.log_pow]
    push_cast; ring
  have h3 : Real.log ((1 + xc) ^ 3714 * (2 + 6 * xc + 9 * xc ^ 2 + 6 * xc ^ 3 + 2 * xc ^ 4) ^ 3714 / (xc ^ 5570 * (1 - xc) ^ 7430)) ≤
      15979.97420422751 := by
    calc _ = _ := l1
      _ = 3714 * Real.log (1 + xc) + 3714 * Real.log (2 + 6 * xc + 9 * xc ^ 2 + 6 * xc ^ 3 + 2 * xc ^ 4) - 7430 * Real.log (1 - xc) -
          5570 * Real.log xc := by ring
      _ ≤ _ := sigma_log
  exact h2.trans (exp_step _ _ n hσ h3)

end BaiCert

theorem solution (n : ℕ) :
    (PiIrrationality.Bai.coef n : ℝ) ≤ Real.exp (15979.97420422751 * (n : ℝ)) := by
  exact BaiCert.coef_le_aux n

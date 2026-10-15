-- Prove2me | solution 1 for PiIrrationality.Bai.coef_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T20:15:22.884406+00:00
-- url     : https://prove2.me/submissions/46950789-3ceb-4367-b30a-68270d6b4c6c

import Definitions.Def_PiIrrationality_BaiForms
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic
set_option autoImplicit false

namespace BaiCertLow
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

lemma hCn (n : ℕ) : (C n : ℕ[X]) = (n : ℕ[X]) := by
  have := Polynomial.C_eq_natCast (R := ℕ) n
  simpa using this

lemma coeff_mul_ge (p q : ℕ[X]) (i j : ℕ) : p.coeff i * q.coeff j ≤ (p * q).coeff (i + j) := by
  rw [Polynomial.coeff_mul]
  exact Finset.single_le_sum (f := fun x : ℕ × ℕ => p.coeff x.1 * q.coeff x.2)
    (fun _ _ => Nat.zero_le _) (a := (i, j)) (Finset.mem_antidiagonal.2 rfl)

lemma coeff_A2 (M u1 u2 : ℕ) (h : u1 + u2 ≤ M) :
    M.choose u2 * (M - u2).choose u1 * 2 ^ (M - u2) ≤
      ((X ^ 2 + 2 * (1 + X) : ℕ[X]) ^ M).coeff (u1 + 2 * u2) := by
  rw [add_pow, Polynomial.finsetSum_coeff]
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun k => (((X ^ 2 : ℕ[X]) ^ k * (2 * (1 + X)) ^ (M - k) * (M.choose k : ℕ[X]))).coeff
      (u1 + 2 * u2)) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (show u2 < M + 1 by omega)))
  have e : ((X ^ 2 : ℕ[X]) ^ u2 * (2 * (1 + X)) ^ (M - u2) * (M.choose u2 : ℕ[X])) =
      X ^ (2 * u2) * (C (2 ^ (M - u2) * M.choose u2) * (1 + X) ^ (M - u2)) := by
    simp only [map_mul, map_pow, map_natCast, ← pow_mul, mul_pow]
    rw [show (C 2 : ℕ[X]) = 2 from rfl, hCn]
    ring
  rw [e, Polynomial.coeff_X_pow_mul', if_pos (by omega), Polynomial.coeff_C_mul,
    Polynomial.coeff_one_add_X_pow, show u1 + 2 * u2 - 2 * u2 = u1 by omega]
  simp only [Nat.cast_id]
  apply le_of_eq
  ring

lemma coeff_A3 (M v1 v2 : ℕ) (h : v1 + v2 ≤ M) :
    M.choose (v1 + v2) * (v1 + v2).choose v2 * 2 ^ (v1 + v2) ≤
      ((2 * X * (1 + X) + 1 : ℕ[X]) ^ M).coeff (v1 + 2 * v2) := by
  rw [add_pow, Polynomial.finsetSum_coeff]
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun k => (((2 * X * (1 + X) : ℕ[X]) ^ k * 1 ^ (M - k) * (M.choose k : ℕ[X]))).coeff
      (v1 + 2 * v2)) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (show v1 + v2 < M + 1 by omega)))
  have e : ((2 * X * (1 + X) : ℕ[X]) ^ (v1 + v2) * 1 ^ (M - (v1 + v2)) * (M.choose (v1 + v2) : ℕ[X])) =
      X ^ (v1 + v2) * (C (2 ^ (v1 + v2) * M.choose (v1 + v2)) * (1 + X) ^ (v1 + v2)) := by
    simp only [map_mul, map_pow, map_natCast, one_pow, mul_pow]
    rw [show (C 2 : ℕ[X]) = 2 from rfl, hCn]
    ring
  rw [e, Polynomial.coeff_X_pow_mul', if_pos (by omega), Polynomial.coeff_C_mul,
    Polynomial.coeff_one_add_X_pow, show v1 + 2 * v2 - (v1 + v2) = v2 by omega]
  simp only [Nat.cast_id]
  apply le_of_eq
  ring


lemma A_fact : PiIrrationality.Bai.A =
    (1 + X) ^ 3714 * ((X ^ 2 + 2 * (1 + X)) * (2 * X * (1 + X) + 1)) ^ 3714 := by
  unfold PiIrrationality.Bai.A
  congr 2
  simp only [map_ofNat]
  ring

lemma coeff_An_lower (N j u1 u2 v1 v2 : ℕ) (hj : j ≤ 3714 * N) (hu : u1 + u2 ≤ 3714 * N)
    (hv : v1 + v2 ≤ 3714 * N) :
    (3714 * N).choose j * ((3714 * N).choose u2 * (3714 * N - u2).choose u1 * 2 ^ (3714 * N - u2)) *
      ((3714 * N).choose (v1 + v2) * (v1 + v2).choose v2 * 2 ^ (v1 + v2)) ≤
    (PiIrrationality.Bai.A ^ N).coeff (j + ((u1 + 2 * u2) + (v1 + 2 * v2))) := by
  have hA : PiIrrationality.Bai.A ^ N = (1 + X) ^ (3714 * N) *
      (((X ^ 2 + 2 * (1 + X)) ^ (3714 * N)) * ((2 * X * (1 + X) + 1) ^ (3714 * N))) := by
    have key : ∀ (p q : ℕ[X]) (k n : ℕ), ((p * q) ^ k) ^ n = p ^ (k * n) * q ^ (k * n) := by
      intro p q k n; rw [← pow_mul, mul_pow]
    rw [A_fact, mul_pow, ← pow_mul, key, mul_comm 3714 N]
  rw [hA]
  have h1 := coeff_mul_ge ((1 + X) ^ (3714 * N) : ℕ[X])
    (((X ^ 2 + 2 * (1 + X)) ^ (3714 * N)) * ((2 * X * (1 + X) + 1) ^ (3714 * N))) j
    ((u1 + 2 * u2) + (v1 + 2 * v2))
  have h2 := coeff_mul_ge (((X ^ 2 + 2 * (1 + X)) ^ (3714 * N) : ℕ[X]))
    ((2 * X * (1 + X) + 1) ^ (3714 * N)) (u1 + 2 * u2) (v1 + 2 * v2)
  have h3 := coeff_A2 (3714 * N) u1 u2 hu
  have h4 := coeff_A3 (3714 * N) v1 v2 hv
  rw [Polynomial.coeff_one_add_X_pow, Nat.cast_id] at h1
  refine le_trans ?_ h1
  have h5 := Nat.mul_le_mul h3 h4
  have h6 := Nat.mul_le_mul_left ((3714 * N).choose j) (le_trans h5 h2)
  rw [mul_assoc]
  exact h6

lemma coef_term_ge (N j u1 u2 v1 v2 m : ℕ) (hj : j ≤ 3714 * N) (hu : u1 + u2 ≤ 3714 * N)
    (hv : v1 + v2 ≤ 3714 * N) (hm : j + ((u1 + 2 * u2) + (v1 + 2 * v2)) + m = 5570 * N) :
    (3714 * N).choose j * ((3714 * N).choose u2 * (3714 * N - u2).choose u1 * 2 ^ (3714 * N - u2)) *
      ((3714 * N).choose (v1 + v2) * (v1 + v2).choose v2 * 2 ^ (v1 + v2)) *
      (7430 * N - 1 + m).choose m ≤ PiIrrationality.Bai.coef N := by
  unfold PiIrrationality.Bai.coef
  have hk : j + ((u1 + 2 * u2) + (v1 + 2 * v2)) ∈ Finset.range (5570 * N + 1) :=
    Finset.mem_range.2 (by omega)
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun k => (PiIrrationality.Bai.A ^ N).coeff k *
      Nat.choose (7430 * N - 1 + (5570 * N - k)) (5570 * N - k)) (fun _ _ => Nat.zero_le _) hk)
  have e : 5570 * N - (j + ((u1 + 2 * u2) + (v1 + 2 * v2))) = m := by omega
  simp only [e]
  exact Nat.mul_le_mul_right _ (coeff_An_lower N j u1 u2 v1 v2 hj hu hv)


/-! ## `coef n ≥ 1` and supermultiplicativity -/

lemma coef_one_le (n : ℕ) : 1 ≤ PiIrrationality.Bai.coef n := by
  have h := coef_term_ge n 0 0 0 0 0 (5570 * n) (by omega) (by omega) (by omega) (by omega)
  refine le_trans ?_ h
  simp only [Nat.choose_zero_right, Nat.sub_zero, Nat.zero_add, mul_zero, Nat.mul_one, one_mul]
  have h1 : 0 < (7430 * n - 1 + 5570 * n).choose (5570 * n) := Nat.choose_pos (by omega)
  have h2 : 0 < 2 ^ (3714 * n) := by positivity
  nlinarith

lemma coef_zero : PiIrrationality.Bai.coef 0 = 1 := by
  simp [PiIrrationality.Bai.coef]

lemma coef_eq_coeff' (n : ℕ) (hn : 1 ≤ n) :
    (PiIrrationality.Bai.coef n : ℤ) = PowerSeries.coeff (5570 * n)
      ((((PiIrrationality.Bai.A ^ n).map (Nat.castRingHom ℤ) : ℤ[X]) : PowerSeries ℤ) *
        (PowerSeries.invOneSubPow ℤ (7430 * n)).val) := by
  rw [PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos _ _ (by omega),
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  unfold PiIrrationality.Bai.coef
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.coeff_map, PowerSeries.coeff_mk, Nat.choose_symm_add]
  simp

/-- the power series `A^n (1-z)^{-7430 n}` over `ℤ` -/
noncomputable def FS (n : ℕ) : PowerSeries ℤ :=
  ((((PiIrrationality.Bai.A ^ n).map (Nat.castRingHom ℤ) : ℤ[X]) : PowerSeries ℤ) *
    (PowerSeries.invOneSubPow ℤ (7430 * n)).val)

lemma FS_nonneg (n : ℕ) (hn : 1 ≤ n) (k : ℕ) : 0 ≤ PowerSeries.coeff k (FS n) := by
  unfold FS
  rw [PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos _ _ (by omega),
    PowerSeries.coeff_mul]
  apply Finset.sum_nonneg
  intro x _
  rw [Polynomial.coeff_coe, Polynomial.coeff_map, PowerSeries.coeff_mk]
  exact mul_nonneg (by simp) (Nat.cast_nonneg _)

lemma FS_add (n1 n2 : ℕ) : FS (n1 + n2) = FS n1 * FS n2 := by
  unfold FS
  rw [pow_add, Polynomial.map_mul, Polynomial.coe_mul, show 7430 * (n1 + n2) = 7430 * n1 + 7430 * n2 by ring,
    PowerSeries.invOneSubPow_add, Units.val_mul]
  ring

lemma coef_super (n1 n2 : ℕ) :
    PiIrrationality.Bai.coef n1 * PiIrrationality.Bai.coef n2 ≤ PiIrrationality.Bai.coef (n1 + n2) := by
  rcases Nat.eq_zero_or_pos n1 with rfl | h1
  · simp [coef_zero]
  rcases Nat.eq_zero_or_pos n2 with rfl | h2
  · simp [coef_zero]
  have e1 := coef_eq_coeff' n1 h1
  have e2 := coef_eq_coeff' n2 h2
  have e12 := coef_eq_coeff' (n1 + n2) (by omega)
  change (PiIrrationality.Bai.coef n1 : ℤ) = PowerSeries.coeff (5570 * n1) (FS n1) at e1
  change (PiIrrationality.Bai.coef n2 : ℤ) = PowerSeries.coeff (5570 * n2) (FS n2) at e2
  change (PiIrrationality.Bai.coef (n1 + n2) : ℤ) = PowerSeries.coeff (5570 * (n1 + n2)) (FS (n1 + n2)) at e12
  have key : (PiIrrationality.Bai.coef n1 : ℤ) * PiIrrationality.Bai.coef n2 ≤
      PiIrrationality.Bai.coef (n1 + n2) := by
    rw [e1, e2, e12, FS_add, PowerSeries.coeff_mul,
      show 5570 * (n1 + n2) = 5570 * n1 + 5570 * n2 by ring]
    exact Finset.single_le_sum (f := fun x : ℕ × ℕ => PowerSeries.coeff x.1 (FS n1) * PowerSeries.coeff x.2 (FS n2))
      (fun x _ => mul_nonneg (FS_nonneg n1 h1 _) (FS_nonneg n2 h2 _)) (a := (5570 * n1, 5570 * n2))
      (Finset.mem_antidiagonal.2 rfl)
  exact_mod_cast key

lemma coef_pow_le (N0 q : ℕ) :
    (PiIrrationality.Bai.coef N0) ^ q ≤ PiIrrationality.Bai.coef (N0 * q) := by
  induction q with
  | zero => simp [coef_zero]
  | succ q ih =>
    rw [pow_succ, Nat.mul_succ]
    calc PiIrrationality.Bai.coef N0 ^ q * PiIrrationality.Bai.coef N0
        ≤ PiIrrationality.Bai.coef (N0 * q) * PiIrrationality.Bai.coef N0 :=
          Nat.mul_le_mul_right _ ih
      _ ≤ PiIrrationality.Bai.coef (N0 * q + N0) := coef_super _ _

lemma coef_floor (N0 n : ℕ) (hN0 : 0 < N0) :
    (PiIrrationality.Bai.coef N0) ^ (n / N0) ≤ PiIrrationality.Bai.coef n := by
  have hn : n = N0 * (n / N0) + n % N0 := (Nat.div_add_mod n N0).symm
  calc (PiIrrationality.Bai.coef N0) ^ (n / N0) ≤ PiIrrationality.Bai.coef (N0 * (n / N0)) :=
        coef_pow_le _ _
    _ = PiIrrationality.Bai.coef (N0 * (n / N0)) * 1 := (mul_one _).symm
    _ ≤ PiIrrationality.Bai.coef (N0 * (n / N0)) * PiIrrationality.Bai.coef (n % N0) :=
        Nat.mul_le_mul_left _ (coef_one_le _)
    _ ≤ PiIrrationality.Bai.coef (N0 * (n / N0) + n % N0) := coef_super _ _
    _ = PiIrrationality.Bai.coef n := by rw [← hn]

/-- from one good value to all large `n` -/
lemma coef_ge_of_one (N0 : ℕ) (hN0 : 0 < N0) (c0 c : ℝ) (hc : 0 < c) (hcc : c < c0)
    (h0 : Real.exp (c0 * N0) ≤ (PiIrrationality.Bai.coef N0 : ℝ)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Real.exp (c * n) ≤ (PiIrrationality.Bai.coef n : ℝ) := by
  refine ⟨⌈c0 * N0 / (c0 - c)⌉₊, fun n hn => ?_⟩
  have hq := coef_floor N0 n hN0
  have hq' : ((PiIrrationality.Bai.coef N0 : ℝ)) ^ (n / N0) ≤ (PiIrrationality.Bai.coef n : ℝ) := by
    exact_mod_cast hq
  refine le_trans ?_ hq'
  have h1 : Real.exp (c0 * N0) ^ (n / N0) ≤ ((PiIrrationality.Bai.coef N0 : ℝ)) ^ (n / N0) :=
    pow_le_pow_left₀ (Real.exp_pos _).le h0 _
  refine le_trans ?_ h1
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  have hr : ((n : ℝ)) < (N0 : ℝ) * ((n / N0 : ℕ) : ℝ) + N0 := by
    have : n < N0 * (n / N0) + N0 := by
      have := Nat.lt_mul_div_succ n hN0
      linarith [Nat.mul_succ N0 (n / N0)]
    exact_mod_cast this
  have hN : c0 * N0 / (c0 - c) ≤ n := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have hd : 0 < c0 - c := by linarith
  have hN' : c0 * N0 ≤ (c0 - c) * n := by
    rw [div_le_iff₀ hd] at hN
    linarith
  have : (0 : ℝ) < N0 := by exact_mod_cast hN0
  nlinarith


/-! ## Entropy bound `m^m ≤ (m+1) C(m,j) j^j (m-j)^(m-j)` for `m = j + d` -/

/-- the binomial term `t_k = C(m,k) j^k d^(m-k)` for `m = j + d` -/
def bt (j d k : ℕ) : ℕ := (j + d).choose k * j ^ k * d ^ (j + d - k)

lemma bt_step (j d k : ℕ) (hk : k < j + d) :
    bt j d (k + 1) * ((k + 1) * d) = bt j d k * ((j + d - k) * j) := by
  unfold bt
  have h1 := Nat.choose_succ_right_eq (j + d) k
  have h2 : d ^ (j + d - k) = d ^ (j + d - (k + 1)) * d := by
    rw [← pow_succ]; congr 1; omega
  rw [h2]
  calc (j + d).choose (k + 1) * j ^ (k + 1) * d ^ (j + d - (k + 1)) * ((k + 1) * d)
      = ((j + d).choose (k + 1) * (k + 1)) * j ^ (k + 1) * (d ^ (j + d - (k + 1)) * d) := by ring
    _ = ((j + d).choose k * (j + d - k)) * j ^ (k + 1) * (d ^ (j + d - (k + 1)) * d) := by rw [h1]
    _ = _ := by ring

lemma bt_up (j d k : ℕ) (hd : 0 < d) (hk : k < j) : bt j d k ≤ bt j d (k + 1) := by
  have hs := bt_step j d k (by omega)
  have hpos : 0 < (k + 1) * d := by positivity
  have hineq : (k + 1) * d ≤ (j + d - k) * j := by
    obtain ⟨e, rfl⟩ : ∃ e, j = k + 1 + e := ⟨j - (k + 1), by omega⟩
    have : k + 1 + e + d - k = 1 + e + d := by omega
    rw [this]
    nlinarith [Nat.zero_le (e * d), Nat.zero_le (k * e), Nat.zero_le (e * e), Nat.zero_le (k * d)]
  have : bt j d k * ((k + 1) * d) ≤ bt j d (k + 1) * ((k + 1) * d) := by
    rw [hs]; exact Nat.mul_le_mul_left _ hineq
  exact Nat.le_of_mul_le_mul_right this hpos

lemma bt_down (j d k : ℕ) (hd : 0 < d) (hk : j ≤ k) (hkm : k < j + d) : bt j d (k + 1) ≤ bt j d k := by
  have hs := bt_step j d k hkm
  have hpos : 0 < (k + 1) * d := by positivity
  have hineq : (j + d - k) * j ≤ (k + 1) * d := by
    obtain ⟨e, rfl⟩ : ∃ e, k = j + e := ⟨k - j, by omega⟩
    obtain ⟨f, rfl⟩ : ∃ f, d = e + 1 + f := ⟨d - (e + 1), by omega⟩
    have : j + (e + 1 + f) - (j + e) = 1 + f := by omega
    rw [this]
    nlinarith [Nat.zero_le (j * f), Nat.zero_le (e * f), Nat.zero_le (j * e), Nat.zero_le (f * f)]
  have : bt j d (k + 1) * ((k + 1) * d) ≤ bt j d k * ((k + 1) * d) := by
    rw [hs]; exact Nat.mul_le_mul_left _ hineq
  exact Nat.le_of_mul_le_mul_right this hpos

lemma bt_le_mode_left (j d : ℕ) (hd : 0 < d) : ∀ i, i ≤ j → bt j d (j - i) ≤ bt j d j := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have h1 := bt_up j d (j - (i + 1)) hd (by omega)
    have e : j - (i + 1) + 1 = j - i := by omega
    rw [e] at h1
    exact le_trans h1 (ih (by omega))

lemma bt_le_mode_right (j d : ℕ) (hd : 0 < d) : ∀ i, j + i ≤ j + d → bt j d (j + i) ≤ bt j d j := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have h1 := bt_down j d (j + i) hd (by omega) (by omega)
    rw [show j + i + 1 = j + (i + 1) from rfl] at h1
    exact le_trans h1 (ih (by omega))

lemma bt_le_mode (j d : ℕ) (hd : 0 < d) (k : ℕ) (hk : k ≤ j + d) : bt j d k ≤ bt j d j := by
  by_cases hkj : k ≤ j
  · have := bt_le_mode_left j d hd (j - k) (by omega)
    rwa [show j - (j - k) = k by omega] at this
  · have := bt_le_mode_right j d hd (k - j) (by omega)
    rwa [show j + (k - j) = k by omega] at this

lemma entropy_nat (j d : ℕ) (hd : 0 < d) :
    (j + d) ^ (j + d) ≤ (j + d + 1) * ((j + d).choose j * j ^ j * d ^ d) := by
  have h : (j + d) ^ (j + d) = ∑ k ∈ Finset.range (j + d + 1), bt j d k := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro k _
    unfold bt
    simp only [Nat.cast_id]
    ring
  rw [h]
  have h2 : ∑ k ∈ Finset.range (j + d + 1), bt j d k ≤ ∑ _k ∈ Finset.range (j + d + 1), bt j d j :=
    Finset.sum_le_sum (fun k hk => bt_le_mode j d hd k (by have := Finset.mem_range.1 hk; omega))
  refine le_trans h2 ?_
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  unfold bt
  rw [show j + d - j = d by omega]

/-- logarithmic form -/
lemma log_choose_ge (j d : ℕ) (hj : 0 < j) (hd : 0 < d) :
    ((j + d : ℕ) : ℝ) * Real.log ((j + d : ℕ) : ℝ) - (j : ℝ) * Real.log j - (d : ℝ) * Real.log d -
      Real.log ((j + d : ℕ) + 1) ≤ Real.log (((j + d).choose j : ℕ) : ℝ) := by
  have h := entropy_nat j d hd
  have hcpos : 0 < (j + d).choose j := Nat.choose_pos (by omega)
  have hr : (((j + d : ℕ) : ℝ)) ^ (j + d) ≤ ((j + d : ℕ) + 1 : ℝ) *
      ((((j + d).choose j : ℕ) : ℝ) * (j : ℝ) ^ j * (d : ℝ) ^ d) := by
    exact_mod_cast h
  have hjp : (0 : ℝ) < j := by exact_mod_cast hj
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hcp : (0 : ℝ) < (((j + d).choose j : ℕ) : ℝ) := by exact_mod_cast hcpos
  have hm : (0 : ℝ) < ((j + d : ℕ) : ℝ) := by positivity
  have hl := Real.log_le_log (by positivity) hr
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul hcp.ne' (by positivity), Real.log_pow, Real.log_pow] at hl
  push_cast at hl ⊢
  linarith


lemma log_choose_ge' (t j d : ℕ) (ht : j + d = t) (hj : 0 < j) (hd : 0 < d) :
    (t : ℝ) * Real.log t - (j : ℝ) * Real.log j - (d : ℝ) * Real.log d - Real.log ((t : ℝ) + 1) ≤
      Real.log ((t.choose j : ℕ) : ℝ) := by
  subst ht
  have := log_choose_ge j d hj hd
  push_cast at this ⊢
  linarith

lemma log_succ_mono (x y : ℕ) (h : x ≤ y) : Real.log ((x : ℝ) + 1) ≤ Real.log ((y : ℝ) + 1) := by
  apply Real.log_le_log (by positivity)
  have : (x : ℝ) ≤ y := by exact_mod_cast h
  linarith

lemma coef_log_lower (N j jj u0 u1 u2 v0 v1 v2 m M T D : ℕ)
    (hj : 0 < j) (hjj : 0 < jj) (hu0 : 0 < u0) (hu1 : 0 < u1) (hu2 : 0 < u2)
    (hv0 : 0 < v0) (hv1 : 0 < v1) (hv2 : 0 < v2) (hm0 : 0 < m) (hD0 : 0 < D)
    (hM : M = 3714 * N) (hjM : j + jj = M) (huM : u0 + u1 + u2 = M) (hvM : v0 + v1 + v2 = M)
    (hmeq : j + ((u1 + 2 * u2) + (v1 + 2 * v2)) + m = 5570 * N)
    (hD : D + 1 = 7430 * N) (hT : T = m + D) (L1 : ℝ) (hL1 : Real.log ((T : ℝ) + 1) ≤ L1) :
    3 * (M : ℝ) * Real.log M - j * Real.log j - jj * Real.log jj - u2 * Real.log u2 -
      u1 * Real.log u1 - u0 * Real.log u0 - v2 * Real.log v2 - v1 * Real.log v1 - v0 * Real.log v0 +
      T * Real.log T - m * Real.log m - D * Real.log D + (u0 + u1 + v1 + v2) * Real.log 2 -
      6 * L1 ≤ Real.log (PiIrrationality.Bai.coef N : ℝ) := by
  have h := coef_term_ge N j u1 u2 v1 v2 m (by omega) (by omega) (by omega) hmeq
  have e5 : (7430 * N - 1 + m) = T := by omega
  rw [← hM, e5] at h
  rw [show M - u2 = u0 + u1 by omega] at h
  have p1 : 0 < M.choose j := Nat.choose_pos (by omega)
  have p2 : 0 < M.choose u2 := Nat.choose_pos (by omega)
  have p3 : 0 < (u0 + u1).choose u1 := Nat.choose_pos (by omega)
  have p4 : 0 < M.choose (v1 + v2) := Nat.choose_pos (by omega)
  have p5 : 0 < (v1 + v2).choose v2 := Nat.choose_pos (by omega)
  have p6 : 0 < T.choose m := Nat.choose_pos (by omega)
  have hcoef : (0 : ℝ) < (PiIrrationality.Bai.coef N : ℝ) := by
    have := coef_one_le N
    exact_mod_cast (Nat.lt_of_lt_of_le one_pos this)
  have hR := (Nat.cast_le (α := ℝ)).2 h
  push_cast at hR
  have q1 : (0 : ℝ) < ((M.choose j : ℕ) : ℝ) := by exact_mod_cast p1
  have q2 : (0 : ℝ) < ((M.choose u2 : ℕ) : ℝ) := by exact_mod_cast p2
  have q3 : (0 : ℝ) < (((u0 + u1).choose u1 : ℕ) : ℝ) := by exact_mod_cast p3
  have q4 : (0 : ℝ) < ((M.choose (v1 + v2) : ℕ) : ℝ) := by exact_mod_cast p4
  have q5 : (0 : ℝ) < (((v1 + v2).choose v2 : ℕ) : ℝ) := by exact_mod_cast p5
  have q6 : (0 : ℝ) < ((T.choose m : ℕ) : ℝ) := by exact_mod_cast p6
  have l1 := log_choose_ge' M j jj hjM hj hjj
  have l2 := log_choose_ge' M u2 (u0 + u1) (by omega) hu2 (by omega)
  have l3 := log_choose_ge' (u0 + u1) u1 u0 (by omega) hu1 hu0
  have l4 := log_choose_ge' M (v1 + v2) v0 (by omega) (by omega) hv0
  have l5 := log_choose_ge' (v1 + v2) v2 v1 (by omega) hv2 hv1
  have l6 := log_choose_ge' T m D hT.symm hm0 hD0
  generalize hb1 : ((M.choose j : ℕ) : ℝ) = b1 at hR q1 l1
  generalize hb2 : ((M.choose u2 : ℕ) : ℝ) = b2 at hR q2 l2
  generalize hb3 : (((u0 + u1).choose u1 : ℕ) : ℝ) = b3 at hR q3 l3
  generalize hb4 : ((M.choose (v1 + v2) : ℕ) : ℝ) = b4 at hR q4 l4
  generalize hb5 : (((v1 + v2).choose v2 : ℕ) : ℝ) = b5 at hR q5 l5
  generalize hb6 : ((T.choose m : ℕ) : ℝ) = b6 at hR q6 l6
  have hlog := Real.log_le_log (by positivity) hR
  rw [Real.log_mul (by positivity) q6.ne', Real.log_mul (by positivity) (by positivity),
    Real.log_mul q1.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul q2.ne' q3.ne', Real.log_mul (by positivity) (by positivity),
    Real.log_mul q4.ne' q5.ne', Real.log_pow, Real.log_pow] at hlog
  have s1 := log_succ_mono M T (by omega)
  have s2 := log_succ_mono (u0 + u1) T (by omega)
  have s3 := log_succ_mono (v1 + v2) T (by omega)
  push_cast at l1 l2 l3 l4 l5 l6 s1 s2 s3 hlog ⊢
  linarith [hlog, l1, l2, l3, l4, l5, l6, s1, s2, s3, hL1]


lemma log_q_M_bounds : (0.006659493420936935208288128698 : ℝ) ≤ Real.log (283355712890625 / 281474976710656 : ℝ) ∧ Real.log (283355712890625 / 281474976710656 : ℝ) ≤ (0.006659493420936935208288128699 : ℝ) := by
  constructor
  · exact le_log_of (283355712890625 / 281474976710656 : ℝ) (1880736179969 / 564830689601281 : ℝ) (333 / 100000 : ℝ) _ 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])
  · exact log_le_of (283355712890625 / 281474976710656 : ℝ) (1880736179969 / 564830689601281 : ℝ) (333 / 100000 : ℝ) _ 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])

lemma log_M_bounds : (45.0612262298173820473283759286 : ℝ) ≤ Real.log (37140000000000000000 : ℝ) ∧ Real.log (37140000000000000000 : ℝ) ≤ (45.0612262298173820473283765787 : ℝ) := by
  obtain ⟨h1, h2⟩ := log_q_M_bounds
  obtain ⟨g1, g2⟩ := log_two_bounds
  have e : Real.log (37140000000000000000 : ℝ) = Real.log (283355712890625 / 281474976710656 : ℝ) + 65 * Real.log (2 : ℝ) := by
    have h : Real.log (37140000000000000000 : ℝ) = Real.log ((283355712890625 / 281474976710656 : ℝ) * 2 ^ 65) := by
      congr 1
      norm_num
    rw [h, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [e]
  constructor <;> linarith

lemma log_q_j_bounds : (-0.252023496552429704742102760832 : ℝ) ≤ Real.log (896081117797878721 / 1152921504606846976 : ℝ) ∧ Real.log (896081117797878721 / 1152921504606846976 : ℝ) ≤ (-0.252023496552429704742098147445 : ℝ) := by
  constructor
  · exact le_log_of (896081117797878721 / 1152921504606846976 : ℝ) (-256840386808968255 / 2049002622404725697 : ℝ) (125349 / 1000000 : ℝ) _ 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])
  · exact log_le_of (896081117797878721 / 1152921504606846976 : ℝ) (-256840386808968255 / 2049002622404725697 : ℝ) (125349 / 1000000 : ℝ) _ 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])

lemma log_j_bounds : (43.4162488787241247885435207991 : ℝ) ≤ Real.log (7168648942383029768 : ℝ) ∧ Real.log (7168648942383029768 : ℝ) ≤ (43.4162488787241247885435260426 : ℝ) := by
  obtain ⟨h1, h2⟩ := log_q_j_bounds
  obtain ⟨g1, g2⟩ := log_two_bounds
  have e : Real.log (7168648942383029768 : ℝ) = Real.log (896081117797878721 / 1152921504606846976 : ℝ) + 63 * Real.log (2 : ℝ) := by
    have h : Real.log (7168648942383029768 : ℝ) = Real.log ((896081117797878721 / 1152921504606846976 : ℝ) * 2 ^ 63) := by
      congr 1
      norm_num
    rw [h, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [e]
  constructor <;> linarith

lemma log_q_jj_bounds : (-0.207793101856905447264251875875 : ℝ) ≤ Real.log (3746418882202121279 / 4611686018427387904 : ℝ) ∧ Real.log (3746418882202121279 / 4611686018427387904 : ℝ) ≤ (-0.207793101856905447264251837421 : ℝ) := by
  constructor
  · exact le_log_of (3746418882202121279 / 4611686018427387904 : ℝ) (-865267136225266625 / 8358104900629509183 : ℝ) (4141 / 40000 : ℝ) _ 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])
  · exact log_le_of (3746418882202121279 / 4611686018427387904 : ℝ) (-865267136225266625 / 8358104900629509183 : ℝ) (4141 / 40000 : ℝ) _ 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])

lemma log_jj_bounds : (44.8467736345395396648558359241 : ℝ) ≤ Real.log (29971351057616970232 : ℝ) ∧ Real.log (29971351057616970232 : ℝ) ≤ (44.8467736345395396648558366126 : ℝ) := by
  obtain ⟨h1, h2⟩ := log_q_jj_bounds
  obtain ⟨g1, g2⟩ := log_two_bounds
  have e : Real.log (29971351057616970232 : ℝ) = Real.log (3746418882202121279 / 4611686018427387904 : ℝ) + 65 * Real.log (2 : ℝ) := by
    have h : Real.log (29971351057616970232 : ℝ) = Real.log ((3746418882202121279 / 4611686018427387904 : ℝ) * 2 ^ 65) := by
      congr 1
      norm_num
    rw [h, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [e]
  constructor <;> linarith

lemma log_q_u0_bounds : (-0.230613935503808391416339286921 : ℝ) ≤ Real.log (1830945325449205159 / 2305843009213693952 : ℝ) ∧ Real.log (1830945325449205159 / 2305843009213693952 : ℝ) ≤ (-0.230613935503808391416338776022 : ℝ) := by
  constructor
  · exact le_log_of (1830945325449205159 / 2305843009213693952 : ℝ) (-474897683764488793 / 4136788334662899111 : ℝ) (114799 / 1000000 : ℝ) _ 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])
  · exact log_le_of (1830945325449205159 / 2305843009213693952 : ℝ) (-474897683764488793 / 4136788334662899111 : ℝ) (114799 / 1000000 : ℝ) _ 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])

lemma log_u0_bounds : (44.823952800892636720703748513 : ℝ) ≤ Real.log (29295125207187282544 : ℝ) ∧ Real.log (29295125207187282544 : ℝ) ≤ (44.823952800892636720703749674 : ℝ) := by
  obtain ⟨h1, h2⟩ := log_q_u0_bounds
  obtain ⟨g1, g2⟩ := log_two_bounds
  have e : Real.log (29295125207187282544 : ℝ) = Real.log (1830945325449205159 / 2305843009213693952 : ℝ) + 65 * Real.log (2 : ℝ) := by
    have h : Real.log (29295125207187282544 : ℝ) = Real.log ((1830945325449205159 / 2305843009213693952 : ℝ) * 2 ^ 65) := by
      congr 1
      norm_num
    rw [h, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [e]
  constructor <;> linarith

lemma log_q_u1_bounds : (-0.27484433019933264886071835349 : ℝ) ≤ Real.log (1751726740060573171 / 2305843009213693952 : ℝ) ∧ Real.log (1751726740060573171 / 2305843009213693952 : ℝ) ≤ (-0.274844330199332648860678934847 : ℝ) := by
  constructor
  · exact le_log_of (1751726740060573171 / 2305843009213693952 : ℝ) (-554116269153120781 / 4057569749274267123 : ℝ) (34141 / 250000 : ℝ) _ 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])
  · exact log_le_of (1751726740060573171 / 2305843009213693952 : ℝ) (-554116269153120781 / 4057569749274267123 : ℝ) (34141 / 250000 : ℝ) _ 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])

lemma log_u1_bounds : (43.3934280450772218444249052065 : ℝ) ≤ Real.log (7006906960242292684 : ℝ) ∧ Real.log (7006906960242292684 : ℝ) ≤ (43.3934280450772218444249452552 : ℝ) := by
  obtain ⟨h1, h2⟩ := log_q_u1_bounds
  obtain ⟨g1, g2⟩ := log_two_bounds
  have e : Real.log (7006906960242292684 : ℝ) = Real.log (1751726740060573171 / 2305843009213693952 : ℝ) + 63 * Real.log (2 : ℝ) := by
    have h : Real.log (7006906960242292684 : ℝ) = Real.log ((1751726740060573171 / 2305843009213693952 : ℝ) * 2 ^ 63) := by
      congr 1
      norm_num
    rw [h, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [e]
  constructor <;> linarith

lemma log_q_u2_bounds : (-0.319074724894856906529865359018 : ℝ) ≤ Real.log (209491958142606193 / 288230376151711744 : ℝ) ∧ Real.log (209491958142606193 / 288230376151711744 : ℝ) ≤ (-0.319074724894856906528298059731 : ℝ) := by
  constructor
  · exact le_log_of (209491958142606193 / 288230376151711744 : ℝ) (-78738418009105551 / 497722334294317937 : ℝ) (79099 / 500000 : ℝ) _ 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])
  · exact log_le_of (209491958142606193 / 288230376151711744 : ℝ) (-78738418009105551 / 497722334294317937 : ℝ) (79099 / 500000 : ℝ) _ 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])

lemma log_u2_bounds : (41.2697561087018616585040618409 : ℝ) ≤ Real.log (837967832570424772 : ℝ) ∧ Real.log (837967832570424772 : ℝ) ≤ (41.2697561087018616585056297403 : ℝ) := by
  obtain ⟨h1, h2⟩ := log_q_u2_bounds
  obtain ⟨g1, g2⟩ := log_two_bounds
  have e : Real.log (837967832570424772 : ℝ) = Real.log (209491958142606193 / 288230376151711744 : ℝ) + 60 * Real.log (2 : ℝ) := by
    have h : Real.log (837967832570424772 : ℝ) = Real.log ((209491958142606193 / 288230376151711744 : ℝ) * 2 ^ 60) := by
      congr 1
      norm_num
    rw [h, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [e]
  constructor <;> linarith

lemma log_q_v0_bounds : (0.234323165100763597499080513031 : ℝ) ≤ Real.log (23317660784639823939 / 18446744073709551616 : ℝ) ∧ Real.log (23317660784639823939 / 18446744073709551616 : ℝ) ≤ (0.234323165100763597499081272015 : ℝ) := by
  constructor
  · exact le_log_of (23317660784639823939 / 18446744073709551616 : ℝ) (4870916710930272323 / 41764404858349375555 : ℝ) (116629 / 1000000 : ℝ) _ 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])
  · exact log_le_of (23317660784639823939 / 18446744073709551616 : ℝ) (4870916710930272323 / 41764404858349375555 : ℝ) (116629 / 1000000 : ℝ) _ 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])

lemma log_v0_bounds : (44.595742720937263400201936193 : ℝ) ≤ Real.log (23317660784639823939 : ℝ) ∧ Real.log (23317660784639823939 : ℝ) ≤ (44.5957427209372634002019375921 : ℝ) := by
  obtain ⟨h1, h2⟩ := log_q_v0_bounds
  obtain ⟨g1, g2⟩ := log_two_bounds
  have e : Real.log (23317660784639823939 : ℝ) = Real.log (23317660784639823939 / 18446744073709551616 : ℝ) + 64 * Real.log (2 : ℝ) := by
    have h : Real.log (23317660784639823939 : ℝ) = Real.log ((23317660784639823939 / 18446744073709551616 : ℝ) * 2 ^ 64) := by
      congr 1
      norm_num
    rw [h, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [e]
  constructor <;> linarith

lemma log_q_v1_bounds : (0.190092770405239340044621068176 : ℝ) ≤ Real.log (11154393674233326205 / 9223372036854775808 : ℝ) ∧ Real.log (11154393674233326205 / 9223372036854775808 : ℝ) ≤ (0.190092770405239340044621072383 : ℝ) := by
  constructor
  · exact le_log_of (11154393674233326205 / 9223372036854775808 : ℝ) (1931021637378550397 / 20377765711088102013 : ℝ) (47381 / 500000 : ℝ) _ 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])
  · exact log_le_of (11154393674233326205 / 9223372036854775808 : ℝ) (1931021637378550397 / 20377765711088102013 : ℝ) (47381 / 500000 : ℝ) _ 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])

lemma log_v1_bounds : (43.8583651456817938333302446281 : ℝ) ≤ Real.log (11154393674233326205 : ℝ) ∧ Real.log (11154393674233326205 : ℝ) ≤ (43.8583651456817938333302452624 : ℝ) := by
  obtain ⟨h1, h2⟩ := log_q_v1_bounds
  obtain ⟨g1, g2⟩ := log_two_bounds
  have e : Real.log (11154393674233326205 : ℝ) = Real.log (11154393674233326205 / 9223372036854775808 : ℝ) + 63 * Real.log (2 : ℝ) := by
    have h : Real.log (11154393674233326205 : ℝ) = Real.log ((11154393674233326205 / 9223372036854775808 : ℝ) * 2 ^ 63) := by
      congr 1
      norm_num
    rw [h, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [e]
  constructor <;> linarith

lemma log_q_v2_bounds : (0.145862375709715082571046128124 : ℝ) ≤ Real.log (41686649080107029 / 36028797018963968 : ℝ) ∧ Real.log (41686649080107029 / 36028797018963968 : ℝ) ≤ (0.145862375709715082571046128131 : ℝ) := by
  constructor
  · exact le_log_of (41686649080107029 / 36028797018963968 : ℝ) (5657852061143061 / 77715446099070997 : ℝ) (72803 / 1000000 : ℝ) _ 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])
  · exact log_le_of (41686649080107029 / 36028797018963968 : ℝ) (5657852061143061 / 77715446099070997 : ℝ) (72803 / 1000000 : ℝ) _ 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])

lemma log_v2_bounds : (42.4278403898663789570222054481 : ℝ) ≤ Real.log (2667945541126849856 : ℝ) ∧ Real.log (2667945541126849856 : ℝ) ≤ (42.4278403898663789570222060582 : ℝ) := by
  obtain ⟨h1, h2⟩ := log_q_v2_bounds
  obtain ⟨g1, g2⟩ := log_two_bounds
  have e : Real.log (2667945541126849856 : ℝ) = Real.log (41686649080107029 / 36028797018963968 : ℝ) + 61 * Real.log (2 : ℝ) := by
    have h : Real.log (2667945541126849856 : ℝ) = Real.log ((41686649080107029 / 36028797018963968 : ℝ) * 2 ^ 61) := by
      congr 1
      norm_num
    rw [h, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [e]
  constructor <;> linarith

lemma log_q_m_bounds : (0.236061231847102029028078345015 : ℝ) ≤ Real.log (23358223675746802087 / 18446744073709551616 : ℝ) ∧ Real.log (23358223675746802087 / 18446744073709551616 : ℝ) ≤ (0.236061231847102029028079256626 : ℝ) := by
  constructor
  · exact le_log_of (23358223675746802087 / 18446744073709551616 : ℝ) (4911479602037250471 / 41804967749456353703 : ℝ) (58743 / 500000 : ℝ) _ 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])
  · exact log_le_of (23358223675746802087 / 18446744073709551616 : ℝ) (4911479602037250471 / 41804967749456353703 : ℝ) (58743 / 500000 : ℝ) _ 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])

lemma log_m_bounds : (44.597480787683601831730934025 : ℝ) ≤ Real.log (23358223675746802087 : ℝ) ∧ Real.log (23358223675746802087 : ℝ) ≤ (44.5974807876836018317309355767 : ℝ) := by
  obtain ⟨h1, h2⟩ := log_q_m_bounds
  obtain ⟨g1, g2⟩ := log_two_bounds
  have e : Real.log (23358223675746802087 : ℝ) = Real.log (23358223675746802087 / 18446744073709551616 : ℝ) + 64 * Real.log (2 : ℝ) := by
    have h : Real.log (23358223675746802087 : ℝ) = Real.log ((23358223675746802087 / 18446744073709551616 : ℝ) * 2 ^ 64) := by
      congr 1
      norm_num
    rw [h, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [e]
  constructor <;> linarith

lemma log_q_D_bounds : (0.006928708660145371613694602827 : ℝ) ≤ Real.log (74299999999999999999 / 73786976294838206464 : ℝ) ∧ Real.log (74299999999999999999 / 73786976294838206464 : ℝ) ≤ (0.006928708660145371613694602828 : ℝ) := by
  constructor
  · exact le_log_of (74299999999999999999 / 73786976294838206464 : ℝ) (513023705161793535 / 148086976294838206463 : ℝ) (693 / 200000 : ℝ) _ 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])
  · exact log_le_of (74299999999999999999 / 73786976294838206464 : ℝ) (513023705161793535 / 148086976294838206463 : ℝ) (693 / 200000 : ℝ) _ 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])

lemma log_D_bounds : (45.7546426256165357931510145228 : ℝ) ≤ Real.log (74299999999999999999 : ℝ) ∧ Real.log (74299999999999999999 : ℝ) ≤ (45.7546426256165357931510151829 : ℝ) := by
  obtain ⟨h1, h2⟩ := log_q_D_bounds
  obtain ⟨g1, g2⟩ := log_two_bounds
  have e : Real.log (74299999999999999999 : ℝ) = Real.log (74299999999999999999 / 73786976294838206464 : ℝ) + 66 * Real.log (2 : ℝ) := by
    have h : Real.log (74299999999999999999 : ℝ) = Real.log ((74299999999999999999 / 73786976294838206464 : ℝ) * 2 ^ 66) := by
      congr 1
      norm_num
    rw [h, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [e]
  constructor <;> linarith

lemma log_q_T_bounds : (0.280291626542626286386722269893 : ℝ) ≤ Real.log (48829111837873401043 / 36893488147419103232 : ℝ) ∧ Real.log (48829111837873401043 / 36893488147419103232 : ℝ) ≤ (0.280291626542626286386786303896 : ℝ) := by
  constructor
  · exact le_log_of (48829111837873401043 / 36893488147419103232 : ℝ) (11935623690454297811 / 85722599985292504275 : ℝ) (34809 / 250000 : ℝ) _ 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])
  · exact log_le_of (48829111837873401043 / 36893488147419103232 : ℝ) (11935623690454297811 / 85722599985292504275 : ℝ) (34809 / 250000 : ℝ) _ 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])

lemma log_T_bounds : (46.0280055434990167079240421898 : ℝ) ≤ Real.log (97658223675746802086 : ℝ) ∧ Real.log (97658223675746802086 : ℝ) ≤ (46.0280055434990167079241068839 : ℝ) := by
  obtain ⟨h1, h2⟩ := log_q_T_bounds
  obtain ⟨g1, g2⟩ := log_two_bounds
  have e : Real.log (97658223675746802086 : ℝ) = Real.log (48829111837873401043 / 36893488147419103232 : ℝ) + 66 * Real.log (2 : ℝ) := by
    have h : Real.log (97658223675746802086 : ℝ) = Real.log ((48829111837873401043 / 36893488147419103232 : ℝ) * 2 ^ 66) := by
      congr 1
      norm_num
    rw [h, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [e]
  constructor <;> linarith


lemma coef_N0_ge :
    Real.exp (15979.9742042274995 * ((10000000000000000 : ℕ) : ℝ)) ≤ (PiIrrationality.Bai.coef 10000000000000000 : ℝ) := by
  have hT1 : Real.log ((((97658223675746802086 : ℕ) : ℝ)) + 1) ≤ 67 * Real.log 2 := by
    have h : (((97658223675746802086 : ℕ) : ℝ)) + 1 ≤ 2 ^ 67 := by norm_num
    calc Real.log ((((97658223675746802086 : ℕ) : ℝ)) + 1) ≤ Real.log (2 ^ 67) := Real.log_le_log (by positivity) h
      _ = 67 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have key := coef_log_lower 10000000000000000 7168648942383029768 29971351057616970232 29295125207187282544 7006906960242292684 837967832570424772 23317660784639823939 11154393674233326205 2667945541126849856 23358223675746802087 37140000000000000000 97658223675746802086 74299999999999999999
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (67 * Real.log 2) hT1
  simp only [Nat.cast_ofNat] at key
  obtain ⟨a_M1, a_M2⟩ := log_M_bounds
  obtain ⟨a_j1, a_j2⟩ := log_j_bounds
  obtain ⟨a_jj1, a_jj2⟩ := log_jj_bounds
  obtain ⟨a_u01, a_u02⟩ := log_u0_bounds
  obtain ⟨a_u11, a_u12⟩ := log_u1_bounds
  obtain ⟨a_u21, a_u22⟩ := log_u2_bounds
  obtain ⟨a_v01, a_v02⟩ := log_v0_bounds
  obtain ⟨a_v11, a_v12⟩ := log_v1_bounds
  obtain ⟨a_v21, a_v22⟩ := log_v2_bounds
  obtain ⟨a_m1, a_m2⟩ := log_m_bounds
  obtain ⟨a_D1, a_D2⟩ := log_D_bounds
  obtain ⟨a_T1, a_T2⟩ := log_T_bounds
  obtain ⟨g1, g2⟩ := log_two_bounds
  have hpos : (0 : ℝ) < (PiIrrationality.Bai.coef 10000000000000000 : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le one_pos (coef_one_le _)
  rw [← Real.le_log_iff_exp_le hpos]
  push_cast
  linarith

end BaiCertLow

theorem solution :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Real.exp (15979.974204227497 * (n : ℝ)) ≤ (PiIrrationality.Bai.coef n : ℝ) := by
  exact BaiCertLow.coef_ge_of_one 10000000000000000 (by norm_num) 15979.9742042274995 15979.974204227497
    (by norm_num) (by norm_num) BaiCertLow.coef_N0_ge

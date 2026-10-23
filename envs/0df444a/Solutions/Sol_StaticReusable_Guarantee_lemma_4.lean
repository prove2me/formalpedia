-- Prove2me | solution 1 for StaticReusable.Guarantee.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T07:57:20.268072+00:00
-- url     : https://prove2.me/submissions/b36fc8a0-5dda-4f31-976e-ef46d884317f

import Mathlib
import Definitions.Def_StaticReusable_Guarantee_Setting

open Finset

namespace SolSRGComb
open StaticReusable.Guarantee

lemma sum_range_split (f : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), f k = f 0 + ∑ k ∈ Finset.Icc 1 n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]
    ring

lemma sum_Icc_shift (g : ℕ → ℝ) (C : ℕ) (hC : 1 ≤ C) :
    ∑ k ∈ Finset.Icc 2 C, g k = ∑ k ∈ Finset.Icc 1 (C - 1), g (k + 1) := by
  have h := Finset.map_add_right_Icc 1 (C - 1) 1
  rw [show C - 1 + 1 = C by omega] at h
  rw [← h, Finset.sum_map]
  rfl

lemma a_zero (C : ℕ) : a C 0 = 1 := by simp [a]

lemma a_succ (C k : ℕ) (hk : k ≤ C) : a C (k + 1) = ((C : ℝ) - k) * a C k := by
  unfold a
  rw [Nat.descFactorial_succ]
  push_cast [Nat.cast_sub hk]
  ring

lemma a_nonneg (C k : ℕ) : 0 ≤ a C k := by unfold a; positivity

lemma a_self_pos (C : ℕ) : 0 < a C C := by
  unfold a
  rw [Nat.descFactorial_self]
  exact_mod_cast Nat.factorial_pos C

lemma zExt_nonneg {C : ℕ} {z : ℕ → ℝ} (hz : ∀ k ∈ Finset.Icc 1 C, 0 ≤ z k) (k : ℕ)
    (hk : 1 ≤ k) : 0 ≤ zExt C z k := by
  unfold zExt
  split_ifs with h
  · exact hz k (by simp [hk, h])
  · norm_num

lemma x_pos {C : ℕ} (hC : 1 ≤ C) {z : ℕ → ℝ} (hz : ∀ k ∈ Finset.Icc 1 C, 0 ≤ z k) :
    0 < xSum C z := by
  unfold xSum
  have h := Finset.single_le_sum (f := fun k => a C k * zExt C z (k + 1))
    (fun k hk => mul_nonneg (a_nonneg C k) (zExt_nonneg hz (k + 1) (by omega)))
    (show C ∈ Finset.Icc 1 C by simp [hC])
  have : zExt C z (C + 1) = 1 := by simp [zExt]
  simp only [this, mul_one] at h
  linarith [a_self_pos C]

lemma u_nonneg {C : ℕ} {z : ℕ → ℝ} (hz : ∀ k ∈ Finset.Icc 1 C, 0 ≤ z k) :
    0 ≤ uSum C z := by
  unfold uSum
  exact Finset.sum_nonneg (fun k hk =>
    mul_nonneg (a_nonneg C k) (zExt_nonneg hz k (Finset.mem_Icc.1 hk).1))

lemma N0_eq {C : ℕ} (hC : 1 ≤ C) (z : ℕ → ℝ) :
    ∑ k ∈ Finset.range (C + 1), a C k * zExt C z (k + 1) = z 1 + xSum C z := by
  rw [sum_range_split, a_zero]
  unfold xSum
  have : zExt C z 1 = z 1 := by simp [zExt, hC]
  rw [this, one_mul]

lemma u_eq {C : ℕ} (hC : 1 ≤ C) (z : ℕ → ℝ) :
    uSum C z = (C : ℝ) * z 1 + ySum C z := by
  unfold uSum ySum
  rw [Finset.Icc_eq_cons_Ioc hC, Finset.sum_cons]
  have h1 : a C 1 = C := by unfold a; simp
  have h2 : zExt C z 1 = z 1 := by simp [zExt, hC]
  have h3 : Finset.Ioc 1 C = Finset.Icc 2 C := by ext j; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [h1, h2, h3]

lemma y_le {C : ℕ} (hC : 1 ≤ C) {z : ℕ → ℝ} (hz : ∀ k ∈ Finset.Icc 1 C, 0 ≤ z k) :
    ySum C z ≤ ((C : ℝ) - 1) * xSum C z := by
  unfold ySum xSum
  rw [sum_Icc_shift (fun k => a C k * zExt C z k) C hC]
  have hsub : ∑ k ∈ Finset.Icc 1 (C - 1), a C k * zExt C z (k + 1) ≤
      ∑ k ∈ Finset.Icc 1 C, a C k * zExt C z (k + 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j; simp only [Finset.mem_Icc]; omega
    · intro k hk _
      exact mul_nonneg (a_nonneg C k) (zExt_nonneg hz (k + 1) (by omega))
  have hC1 : (0 : ℝ) ≤ (C : ℝ) - 1 := by
    have : (1 : ℝ) ≤ C := by exact_mod_cast hC
    linarith
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hsub hC1)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  simp only [Finset.mem_Icc] at hk
  rw [a_succ C k (by omega)]
  have hz' := zExt_nonneg hz (k + 1) (by omega)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk.1
  have ha := a_nonneg C k
  have : ((C : ℝ) - k) ≤ (C : ℝ) - 1 := by linarith
  nlinarith [mul_nonneg ha hz']

/-- the truncated polynomial `q₁(r) = Σ_{i=1}^4 a_i r^{4-i}` -/
noncomputable def q1 (C : ℕ) (r : ℝ) : ℝ := ∑ i ∈ Finset.Icc 1 4, a C i * r ^ (4 - i)

lemma Icc14 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide

lemma q1_expl {C : ℕ} (hC : 4 ≤ C) (r : ℝ) :
    q1 C r = (C : ℝ) * r ^ 3 + (C : ℝ) * ((C : ℝ) - 1) * r ^ 2 +
      (C : ℝ) * ((C : ℝ) - 1) * ((C : ℝ) - 2) * r +
      (C : ℝ) * ((C : ℝ) - 1) * ((C : ℝ) - 2) * ((C : ℝ) - 3) := by
  unfold q1
  rw [Icc14, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num
  have h1 : a C 1 = C := by rw [a_succ C 0 (by omega), a_zero]; simp
  have h2 : a C 2 = C * (C - 1) := by rw [a_succ C 1 (by omega), h1]; push_cast; ring
  have h3 : a C 3 = C * (C - 1) * (C - 2) := by rw [a_succ C 2 (by omega), h2]; push_cast; ring
  have h4 : a C 4 = C * (C - 1) * (C - 2) * (C - 3) := by
    rw [a_succ C 3 (by omega), h3]; push_cast; ring
  rw [h1, h2, h3, h4]
  ring

lemma q1_nonneg {C : ℕ} (r : ℝ) (hr : 0 ≤ r) : 0 ≤ q1 C r := by
  unfold q1
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (a_nonneg C i) (pow_nonneg hr _))

lemma q1_pos {C : ℕ} (hC : 4 ≤ C) (r : ℝ) (hr : 0 ≤ r) : 0 < q1 C r := by
  unfold q1
  have h := Finset.single_le_sum (f := fun i => a C i * r ^ (4 - i))
    (fun i _ => mul_nonneg (a_nonneg C i) (pow_nonneg hr _))
    (show 4 ∈ Finset.Icc 1 4 by simp)
  have : 0 < a C 4 := by unfold a; exact_mod_cast Nat.descFactorial_pos.2 hC
  simp at h
  linarith

lemma keyA (c r : ℝ) (hc : 4 ≤ c) (hr0 : 0 ≤ r) (hr : r ≤ c - 1) :
    104 * r ^ 4 ≤ 27 * (c * r ^ 3 + c * (c - 1) * r ^ 2 + c * (c - 1) * (c - 2) * r +
      c * (c - 1) * (c - 2) * (c - 3)) := by
  set T := c - 1 with hT
  have hT0 : 0 < T := by linarith
  have hTr : r ≤ T := hr
  have e1 : r ^ 1 ≤ T ^ 1 := pow_le_pow_left₀ hr0 hTr 1
  have e2 : r ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hr0 hTr 2
  have e3 : r ^ 3 ≤ T ^ 3 := pow_le_pow_left₀ hr0 hTr 3
  have e4 : r ^ 4 ≤ T ^ 4 := pow_le_pow_left₀ hr0 hTr 4
  have hc0 : 0 ≤ c := by linarith
  have hc1 : 0 ≤ c - 1 := by linarith
  have hc2 : 0 ≤ c - 2 := by linarith
  have hc3 : 0 ≤ c - 3 := by linarith
  have hrT : 0 ≤ r * T := mul_nonneg hr0 hT0.le
  -- T^4 q1(r) ≥ r^4 q1(T)
  have hcmp : T ^ 4 * (c * r ^ 3 + c * (c - 1) * r ^ 2 + c * (c - 1) * (c - 2) * r +
      c * (c - 1) * (c - 2) * (c - 3)) - r ^ 4 * (c * T ^ 3 + c * (c - 1) * T ^ 2 +
      c * (c - 1) * (c - 2) * T + c * (c - 1) * (c - 2) * (c - 3)) =
      c * (r * T) ^ 3 * (T ^ 1 - r ^ 1) + c * (c - 1) * (r * T) ^ 2 * (T ^ 2 - r ^ 2) +
      c * (c - 1) * (c - 2) * (r * T) * (T ^ 3 - r ^ 3) +
      c * (c - 1) * (c - 2) * (c - 3) * (T ^ 4 - r ^ 4) := by ring
  have hcmp0 : 0 ≤ c * (r * T) ^ 3 * (T ^ 1 - r ^ 1) + c * (c - 1) * (r * T) ^ 2 * (T ^ 2 - r ^ 2) +
      c * (c - 1) * (c - 2) * (r * T) * (T ^ 3 - r ^ 3) +
      c * (c - 1) * (c - 2) * (c - 3) * (T ^ 4 - r ^ 4) := by
    have s1 : 0 ≤ T ^ 1 - r ^ 1 := by linarith
    have s2 : 0 ≤ T ^ 2 - r ^ 2 := by linarith
    have s3 : 0 ≤ T ^ 3 - r ^ 3 := by linarith
    have s4 : 0 ≤ T ^ 4 - r ^ 4 := by linarith
    positivity
  -- 27 q1(T) ≥ 104 T^4
  have hpolyT : 27 * (c * T ^ 3 + c * (c - 1) * T ^ 2 + c * (c - 1) * (c - 2) * T +
      c * (c - 1) * (c - 2) * (c - 3)) - 104 * T ^ 4 =
      4 * (c - 4) ^ 4 + 48 * (c - 4) ^ 3 + 162 * (c - 4) ^ 2 + 162 * (c - 4) := by
    rw [hT]; ring
  have hm : 0 ≤ c - 4 := by linarith
  have hpolyT0 : 0 ≤ 4 * (c - 4) ^ 4 + 48 * (c - 4) ^ 3 + 162 * (c - 4) ^ 2 + 162 * (c - 4) := by
    positivity
  have hT4 : 0 < T ^ 4 := by positivity
  have hr4 : 0 ≤ r ^ 4 := by positivity
  -- combine
  have : T ^ 4 * (104 * r ^ 4) ≤ T ^ 4 * (27 * (c * r ^ 3 + c * (c - 1) * r ^ 2 +
      c * (c - 1) * (c - 2) * r + c * (c - 1) * (c - 2) * (c - 3))) := by
    nlinarith [mul_nonneg hr4 hpolyT0]
  exact le_of_mul_le_mul_left this hT4

lemma keyB (c r : ℝ) (hc : 4 ≤ c) (hr : c - 1 ≤ r) :
    104 * c * (r ^ 4 + (c * r ^ 3 + c * (c - 1) * r ^ 2 + c * (c - 1) * (c - 2) * r +
      c * (c - 1) * (c - 2) * (c - 3))) ≤
    131 * (r + 1) * (c * r ^ 3 + c * (c - 1) * r ^ 2 + c * (c - 1) * (c - 2) * r +
      c * (c - 1) * (c - 2) * (c - 3)) := by
  set m := c - 4 with hm
  set sg := r - c + 1 with hsg
  have hm0 : 0 ≤ m := by linarith
  have hsg0 : 0 ≤ sg := by linarith
  have hc' : c = m + 4 := by rw [hm]; ring
  have hr' : r = m + 3 + sg := by rw [hm, hsg]; ring
  have key : 131 * (r + 1) * (c * r ^ 3 + c * (c - 1) * r ^ 2 + c * (c - 1) * (c - 2) * r +
      c * (c - 1) * (c - 2) * (c - 3)) - 104 * c * (r ^ 4 + (c * r ^ 3 + c * (c - 1) * r ^ 2 +
      c * (c - 1) * (c - 2) * r + c * (c - 1) * (c - 2) * (c - 3))) =
      4*m^5 + 270*m^4*sg + 64*m^4 + 270*m^3*sg^2 + 3121*m^3*sg + 354*m^3 + 135*m^2*sg^3 +
      2677*m^2*sg^2 + 13355*m^2*sg + 810*m^2 + 27*m*sg^4 + 972*m*sg^3 + 8749*m*sg^2 +
      25258*m*sg + 648*m + 108*sg^4 + 1728*sg^3 + 9444*sg^2 + 17976*sg := by
    rw [hr', hc']; ring
  have : 0 ≤ 4*m^5 + 270*m^4*sg + 64*m^4 + 270*m^3*sg^2 + 3121*m^3*sg + 354*m^3 + 135*m^2*sg^3 +
      2677*m^2*sg^2 + 13355*m^2*sg + 810*m^2 + 27*m*sg^4 + 972*m*sg^3 + 8749*m*sg^2 +
      25258*m*sg + 648*m + 108*sg^4 + 1728*sg^3 + 9444*sg^2 + 17976*sg := by positivity
  linarith

/-- the one-variable bound: `104 (r⁴ + q₁(r)) ≤ 131 (1 + s) q₁(r)` when `0 ≤ r ≤ C s + C - 1`. -/
lemma main_bound {C : ℕ} (hC : 4 ≤ C) (r s : ℝ) (hr0 : 0 ≤ r) (hs : 0 ≤ s)
    (hrs : r ≤ (C : ℝ) * s + ((C : ℝ) - 1)) :
    104 * (r ^ 4 + q1 C r) ≤ 131 * (1 + s) * q1 C r := by
  have hq := q1_nonneg (C := C) r hr0
  have hc : (4 : ℝ) ≤ C := by exact_mod_cast hC
  rcases le_total r ((C : ℝ) - 1) with h | h
  · have := keyA C r hc hr0 h
    rw [← q1_expl hC r] at this
    nlinarith
  · have hB := keyB C r hc h
    rw [← q1_expl hC r] at hB
    have hcs : r + 1 ≤ (C : ℝ) * (1 + s) := by linarith
    have hc0 : (0 : ℝ) < C := by linarith
    have : (C : ℝ) * (104 * (r ^ 4 + q1 C r)) ≤ (C : ℝ) * (131 * (1 + s) * q1 C r) := by
      nlinarith [mul_le_mul_of_nonneg_right hcs hq]
    exact le_of_mul_le_mul_left this hc0

/-- `Σ_{i=1}^4 a_i u^{4-i} x^{i-1} = x^3 q₁(u/x)` -/
lemma Q1_eq {C : ℕ} (u x : ℝ) (hx : x ≠ 0) :
    ∑ i ∈ Finset.Icc 1 4, a C i * u ^ (4 - i) * x ^ (i - 1) = x ^ 3 * q1 C (u / x) := by
  unfold q1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_Icc] at hi
  rw [div_pow]
  have : x ^ 3 = x ^ (4 - i) * x ^ (i - 1) := by rw [← pow_add]; congr 1; omega
  rw [this]
  field_simp

lemma Q0_eq {C : ℕ} (u x : ℝ) (hx : x ≠ 0) :
    ∑ i ∈ Finset.range 5, a C i * u ^ (4 - i) * x ^ i = x ^ 4 * ((u / x) ^ 4 + q1 C (u / x)) := by
  rw [sum_range_split (fun i => a C i * u ^ (4 - i) * x ^ i) 4, a_zero, mul_add]
  congr 1
  · field_simp
  · unfold q1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_Icc] at hi
    rw [div_pow]
    have : x ^ 4 = x ^ (4 - i) * x ^ i := by rw [← pow_add]; congr 1; omega
    rw [this]
    field_simp

lemma Rt_eq {C : ℕ} (hC : 4 ≤ C) (z : ℕ → ℝ) (hz : ∀ k ∈ Finset.Icc 1 C, 0 ≤ z k) :
    Rt C z = (z 1 + xSum C z) * q1 C (uSum C z / xSum C z) /
      (xSum C z * ((uSum C z / xSum C z) ^ 4 + q1 C (uSum C z / xSum C z))) := by
  have hx := x_pos (by omega) hz
  unfold Rt
  rw [N0_eq (by omega), Q1_eq _ _ hx.ne', Q0_eq _ _ hx.ne']
  have hq := q1_pos hC (uSum C z / xSum C z) (div_nonneg (u_nonneg hz) hx.le)
  have : 0 < (uSum C z / xSum C z) ^ 4 + q1 C (uSum C z / xSum C z) := by positivity
  field_simp

lemma Rt_bound {C : ℕ} (hC : 4 ≤ C) (z : ℕ → ℝ) (hz : ∀ k ∈ Finset.Icc 1 C, 0 ≤ z k) :
    (104 / 131 : ℝ) ≤ Rt C z := by
  have hx := x_pos (by omega) hz
  set x := xSum C z
  set r := uSum C z / x with hr
  set s := z 1 / x with hs
  have hr0 : 0 ≤ r := div_nonneg (u_nonneg hz) hx.le
  have hs0 : 0 ≤ s := div_nonneg (hz 1 (by simp; omega)) hx.le
  have hrs : r ≤ (C : ℝ) * s + ((C : ℝ) - 1) := by
    rw [hr, hs, div_le_iff₀ hx, u_eq (by omega)]
    have := y_le (by omega) hz
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ hx.ne']
    linarith
  have hmain := main_bound hC r s hr0 hs0 hrs
  rw [Rt_eq hC z hz]
  have hq := q1_pos hC r hr0
  have hden : 0 < x * (r ^ 4 + q1 C r) := by positivity
  rw [le_div_iff₀ hden]
  have : z 1 + x = x * (1 + s) := by rw [hs]; field_simp; ring
  rw [this]
  have := mul_le_mul_of_nonneg_left hmain hx.le
  nlinarith

lemma S0_eq {C : ℕ} (r : ℝ) :
    ∑ i ∈ Finset.range (C + 1), a C i * r ^ (C - i) =
      r ^ C + ∑ i ∈ Finset.Icc 1 C, a C i * r ^ (C - i) := by
  rw [sum_range_split (fun i => a C i * r ^ (C - i)) C, a_zero]
  simp

lemma step2b {C : ℕ} (hC : 4 ≤ C) (z : ℕ → ℝ) (hz : ∀ k ∈ Finset.Icc 1 C, 0 ≤ z k) :
    Rt C z ≤ R C z := by
  have hx := x_pos (by omega) hz
  set x := xSum C z
  set r := uSum C z / x with hr
  have hr0 : 0 ≤ r := div_nonneg (u_nonneg hz) hx.le
  rw [Rt_eq hC z hz]
  unfold R
  rw [N0_eq (by omega), S0_eq]
  rw [← hr]
  set S1 := ∑ i ∈ Finset.Icc 1 C, a C i * r ^ (C - i) with hS1
  have hq := q1_pos hC r hr0
  have hS1pos : 0 < S1 := by
    have h := Finset.single_le_sum (f := fun i => a C i * r ^ (C - i))
      (fun i _ => mul_nonneg (a_nonneg C i) (pow_nonneg hr0 _))
      (show C ∈ Finset.Icc 1 C by simp; omega)
    simp only [Nat.sub_self, pow_zero, mul_one] at h
    linarith [a_self_pos C]
  have hN0 : 0 ≤ z 1 + x := by linarith [hz 1 (by simp; omega)]
  -- key: q1 r^C ≤ S1 r^4
  have hkey : q1 C r * r ^ C ≤ S1 * r ^ 4 := by
    have hsub : ∑ i ∈ Finset.Icc 1 4, a C i * r ^ (C - i) ≤ S1 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j; simp only [Finset.mem_Icc]; omega
      · intro i _ _; exact mul_nonneg (a_nonneg C i) (pow_nonneg hr0 _)
    have heq : q1 C r * r ^ C = (∑ i ∈ Finset.Icc 1 4, a C i * r ^ (C - i)) * r ^ 4 := by
      unfold q1
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_Icc] at hi
      rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add]
      congr 2
      omega
    rw [heq]
    exact mul_le_mul_of_nonneg_right hsub (pow_nonneg hr0 4)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : q1 C r * (r ^ C + S1) ≤ S1 * (r ^ 4 + q1 C r) := by nlinarith
  have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hN0 hx.le)
  nlinarith


lemma keyC (c r : ℝ) (hc : 4 ≤ c) (hr0 : 0 ≤ r) (hr : r ≤ 2 * c - 2) :
    12 * c * (r ^ 4 + (c * r ^ 3 + c * (c - 1) * r ^ 2 + c * (c - 1) * (c - 2) * r +
      c * (c - 1) * (c - 2) * (c - 3))) ≤
    7 * (2 * c + r) * (c * r ^ 3 + c * (c - 1) * r ^ 2 + c * (c - 1) * (c - 2) * r +
      c * (c - 1) * (c - 2) * (c - 3)) := by
  have hc0 : 0 ≤ c := by linarith
  have hc1 : 0 ≤ c - 1 := by linarith
  have hc2 : 0 ≤ c - 2 := by linarith
  have hc3 : 0 ≤ c - 3 := by linarith
  set b3 := 7 * (c * (c - 1)) + 2 * c * c with hb3
  set b2 := 7 * (c * (c - 1) * (c - 2)) + 2 * c * (c * (c - 1)) with hb2
  set b1 := 7 * (c * (c - 1) * (c - 2) * (c - 3)) + 2 * c * (c * (c - 1) * (c - 2)) with hb1
  set b0 := 2 * c * (c * (c - 1) * (c - 2) * (c - 3)) with hb0
  have hb3' : 0 ≤ b3 := by positivity
  have hb2' : 0 ≤ b2 := by positivity
  have hb1' : 0 ≤ b1 := by positivity
  have hb0' : 0 ≤ b0 := by positivity
  have hsplit : 7 * (2 * c + r) * (c * r ^ 3 + c * (c - 1) * r ^ 2 + c * (c - 1) * (c - 2) * r +
      c * (c - 1) * (c - 2) * (c - 3)) - 12 * c * (r ^ 4 + (c * r ^ 3 + c * (c - 1) * r ^ 2 +
      c * (c - 1) * (c - 2) * r + c * (c - 1) * (c - 2) * (c - 3))) =
      (b3 * r ^ 3 + b2 * r ^ 2 + b1 * r + b0) - 5 * c * r ^ 4 := by
    rw [hb3, hb2, hb1, hb0]; ring
  set T := 2 * c - 2 with hT
  have hT0 : 0 < T := by linarith
  have e1 : r ^ 1 ≤ T ^ 1 := pow_le_pow_left₀ hr0 hr 1
  have e2 : r ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hr0 hr 2
  have e3 : r ^ 3 ≤ T ^ 3 := pow_le_pow_left₀ hr0 hr 3
  have e4 : r ^ 4 ≤ T ^ 4 := pow_le_pow_left₀ hr0 hr 4
  have hrT : 0 ≤ r * T := mul_nonneg hr0 hT0.le
  have hcmp : T ^ 4 * (b3 * r ^ 3 + b2 * r ^ 2 + b1 * r + b0) -
      r ^ 4 * (b3 * T ^ 3 + b2 * T ^ 2 + b1 * T + b0) =
      b3 * (r * T) ^ 3 * (T ^ 1 - r ^ 1) + b2 * (r * T) ^ 2 * (T ^ 2 - r ^ 2) +
      b1 * (r * T) * (T ^ 3 - r ^ 3) + b0 * (T ^ 4 - r ^ 4) := by ring
  have hcmp0 : 0 ≤ b3 * (r * T) ^ 3 * (T ^ 1 - r ^ 1) + b2 * (r * T) ^ 2 * (T ^ 2 - r ^ 2) +
      b1 * (r * T) * (T ^ 3 - r ^ 3) + b0 * (T ^ 4 - r ^ 4) := by
    have s1 : 0 ≤ T ^ 1 - r ^ 1 := by linarith
    have s2 : 0 ≤ T ^ 2 - r ^ 2 := by linarith
    have s3 : 0 ≤ T ^ 3 - r ^ 3 := by linarith
    have s4 : 0 ≤ T ^ 4 - r ^ 4 := by linarith
    positivity
  set m := c - 4 with hm
  have hm0 : 0 ≤ m := by linarith
  have hpolyT : (b3 * T ^ 3 + b2 * T ^ 2 + b1 * T + b0) - 5 * c * T ^ 4 =
      48 * m ^ 5 + 718 * m ^ 4 + 4268 * m ^ 3 + 12626 * m ^ 2 + 18628 * m + 10992 := by
    have hc' : c = m + 4 := by rw [hm]; ring
    rw [hb3, hb2, hb1, hb0, hT, hc']; ring
  have hpolyT0 : 0 ≤ 48 * m ^ 5 + 718 * m ^ 4 + 4268 * m ^ 3 + 12626 * m ^ 2 + 18628 * m + 10992 := by
    positivity
  have hT4 : 0 < T ^ 4 := by positivity
  have hr4 : 0 ≤ r ^ 4 := by positivity
  have : T ^ 4 * (5 * c * r ^ 4) ≤ T ^ 4 * (b3 * r ^ 3 + b2 * r ^ 2 + b1 * r + b0) := by
    nlinarith [mul_nonneg hr4 hpolyT0]
  have := le_of_mul_le_mul_left this hT4
  linarith

lemma keyD (c r : ℝ) (hc : 4 ≤ c) (hr : 2 * c - 2 ≤ r) :
    6 * c * (r ^ 4 + (c * r ^ 3 + c * (c - 1) * r ^ 2 + c * (c - 1) * (c - 2) * r +
      c * (c - 1) * (c - 2) * (c - 3))) ≤
    7 * (r + 1) * (c * r ^ 3 + c * (c - 1) * r ^ 2 + c * (c - 1) * (c - 2) * r +
      c * (c - 1) * (c - 2) * (c - 3)) := by
  set m := c - 4 with hm
  set sg := r - 2 * c + 2 with hsg
  have hm0 : 0 ≤ m := by linarith
  have hsg0 : 0 ≤ sg := by linarith
  have hc' : c = m + 4 := by rw [hm]; ring
  have hr' : r = 2 * m + 6 + sg := by rw [hm, hsg]; ring
  have key : 7 * (r + 1) * (c * r ^ 3 + c * (c - 1) * r ^ 2 + c * (c - 1) * (c - 2) * r +
      c * (c - 1) * (c - 2) * (c - 3)) - 6 * c * (r ^ 4 + (c * r ^ 3 + c * (c - 1) * r ^ 2 +
      c * (c - 1) * (c - 2) * r + c * (c - 1) * (c - 2) * (c - 3))) =
      24*m^5 + 49*m^4*sg + 359*m^4 + 31*m^3*sg^2 + 611*m^3*sg + 2134*m^3 + 9*m^2*sg^3 +
      310*m^2*sg^2 + 2840*m^2*sg + 6313*m^2 + m*sg^4 + 64*m*sg^3 + 1023*m*sg^2 + 5848*m*sg +
      9314*m + 4*sg^4 + 112*sg^3 + 1116*sg^2 + 4512*sg + 5496 := by
    rw [hr', hc']; ring
  have : 0 ≤ 24*m^5 + 49*m^4*sg + 359*m^4 + 31*m^3*sg^2 + 611*m^3*sg + 2134*m^3 + 9*m^2*sg^3 +
      310*m^2*sg^2 + 2840*m^2*sg + 6313*m^2 + m*sg^4 + 64*m*sg^3 + 1023*m*sg^2 + 5848*m*sg +
      9314*m + 4*sg^4 + 112*sg^3 + 1116*sg^2 + 4512*sg + 5496 := by positivity
  linarith

lemma main_bound4 {C : ℕ} (hC : 4 ≤ C) (r s : ℝ) (hr0 : 0 ≤ r) (hs : 0 ≤ s)
    (hrs : r ≤ (C : ℝ) * s + ((C : ℝ) - 1)) (hrs2 : r ≤ 2 * (C : ℝ) * s) :
    6 * (r ^ 4 + q1 C r) ≤ 7 * (1 + s) * q1 C r := by
  have hq := q1_nonneg (C := C) r hr0
  have hc : (4 : ℝ) ≤ C := by exact_mod_cast hC
  have hc0 : (0 : ℝ) < C := by linarith
  rcases le_total r (2 * (C : ℝ) - 2) with h | h
  · have hK := keyC C r hc hr0 h
    rw [← q1_expl hC r] at hK
    have hcs : 2 * (C : ℝ) + r ≤ 2 * (C : ℝ) * (1 + s) := by linarith
    have : (2 * (C : ℝ)) * (6 * (r ^ 4 + q1 C r)) ≤ (2 * (C : ℝ)) * (7 * (1 + s) * q1 C r) := by
      nlinarith [mul_le_mul_of_nonneg_right hcs hq]
    exact le_of_mul_le_mul_left this (by linarith)
  · have hK := keyD C r hc h
    rw [← q1_expl hC r] at hK
    have hcs : r + 1 ≤ (C : ℝ) * (1 + s) := by linarith
    have : (C : ℝ) * (6 * (r ^ 4 + q1 C r)) ≤ (C : ℝ) * (7 * (1 + s) * q1 C r) := by
      nlinarith [mul_le_mul_of_nonneg_right hcs hq]
    exact le_of_mul_le_mul_left this hc0

lemma Rt_bound4 {C : ℕ} (hC : 4 ≤ C) (z : ℕ → ℝ) (hz : ∀ k ∈ Finset.Icc 1 C, 0 ≤ z k)
    (hy : ySum C z ≤ a C 1 * z 1) :
    (6 / 7 : ℝ) ≤ Rt C z := by
  have hx := x_pos (by omega) hz
  have h1 : a C 1 = C := by unfold a; simp
  rw [h1] at hy
  set x := xSum C z
  set r := uSum C z / x with hr
  set s := z 1 / x with hs
  have hr0 : 0 ≤ r := div_nonneg (u_nonneg hz) hx.le
  have hs0 : 0 ≤ s := div_nonneg (hz 1 (by simp; omega)) hx.le
  have hrs : r ≤ (C : ℝ) * s + ((C : ℝ) - 1) := by
    rw [hr, hs, div_le_iff₀ hx, u_eq (by omega)]
    have := y_le (by omega) hz
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ hx.ne']
    linarith
  have hrs2 : r ≤ 2 * (C : ℝ) * s := by
    rw [hr, hs, div_le_iff₀ hx, u_eq (by omega)]
    rw [mul_assoc, div_mul_cancel₀ _ hx.ne']
    linarith
  have hmain := main_bound4 hC r s hr0 hs0 hrs hrs2
  rw [Rt_eq hC z hz]
  have hq := q1_pos hC r hr0
  have hden : 0 < x * (r ^ 4 + q1 C r) := by positivity
  rw [le_div_iff₀ hden]
  have : z 1 + x = x * (1 + s) := by rw [hs]; field_simp; ring
  rw [this]
  have := mul_le_mul_of_nonneg_left hmain hx.le
  nlinarith

end SolSRGComb

open SolSRGComb in
theorem solution {C : ℕ} (hC : 4 ≤ C) (z : ℕ → ℝ) (hz : ∀ k ∈ Finset.Icc 1 C, 0 ≤ z k)
    (hy : StaticReusable.Guarantee.ySum C z ≤ StaticReusable.Guarantee.a C 1 * z 1) :
    (6 / 7 : ℝ) ≤ StaticReusable.Guarantee.Rt C z :=
  Rt_bound4 hC z hz hy

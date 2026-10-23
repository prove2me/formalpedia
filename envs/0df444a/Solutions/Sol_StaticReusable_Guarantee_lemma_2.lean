-- Prove2me | solution 1 for StaticReusable.Guarantee.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T08:08:45.818396+00:00
-- url     : https://prove2.me/submissions/4dbb6e55-db8a-45f1-a836-af5deafe0c0d

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


/-- `E(r) = 2 q₁(r)(r⁴+q₁(r)) − (2c + r) r³ K(r)` with `K = r⁴ (4q₁ − r q₁')/r⁴`-coefficients. -/
lemma keyE (m r : ℝ) (hm : 0 ≤ m) (hr0 : 0 ≤ r) (hr : r ≤ 2 * m + 6) :
    0 ≤ 2 * ((m + 4) * r ^ 3 + (m + 4) * (m + 3) * r ^ 2 + (m + 4) * (m + 3) * (m + 2) * r +
        (m + 4) * (m + 3) * (m + 2) * (m + 1)) *
        (r ^ 4 + ((m + 4) * r ^ 3 + (m + 4) * (m + 3) * r ^ 2 + (m + 4) * (m + 3) * (m + 2) * r +
        (m + 4) * (m + 3) * (m + 2) * (m + 1))) -
      (2 * (m + 4) + r) * r ^ 3 * ((m + 4) * r ^ 3 + 2 * ((m + 4) * (m + 3)) * r ^ 2 +
        3 * ((m + 4) * (m + 3) * (m + 2)) * r + 4 * ((m + 4) * (m + 3) * (m + 2) * (m + 1))) := by
  set ρ := 2 * m + 6 - r with hρdef
  have hρ : 0 ≤ ρ := by linarith
  have hT : 0 < (2 * m + 6) ^ 7 := by positivity
  have hid : (2 * m + 6) ^ 7 * (2 * ((m + 4) * r ^ 3 + (m + 4) * (m + 3) * r ^ 2 + (m + 4) * (m + 3) * (m + 2) * r +
        (m + 4) * (m + 3) * (m + 2) * (m + 1)) *
        (r ^ 4 + ((m + 4) * r ^ 3 + (m + 4) * (m + 3) * r ^ 2 + (m + 4) * (m + 3) * (m + 2) * r +
        (m + 4) * (m + 3) * (m + 2) * (m + 1))) -
      (2 * (m + 4) + r) * r ^ 3 * ((m + 4) * r ^ 3 + 2 * ((m + 4) * (m + 3)) * r ^ 2 +
        3 * ((m + 4) * (m + 3) * (m + 2)) * r + 4 * ((m + 4) * (m + 3) * (m + 2) * (m + 1)))) =
      (2*m^8 + 40*m^7 + 340*m^6 + 1600*m^5 + 4546*m^4 + 7960*m^3 + 8360*m^2 + 4800*m + 1152) * r ^ 0 * ρ ^ 7 + (22*m^8 + 456*m^7 + 4044*m^6 + 20016*m^5 + 60390*m^4 + 113544*m^3 + 129656*m^2 + 81984*m + 21888) * r ^ 1 * ρ ^ 6 + (114*m^8 + 2456*m^7 + 22772*m^6 + 118624*m^5 + 379474*m^4 + 762696*m^3 + 939336*m^2 + 646848*m + 190080) * r ^ 2 * ρ ^ 5 + (310*m^8 + 6904*m^7 + 66508*m^6 + 362064*m^5 + 1218726*m^4 + 2598392*m^3 + 3428056*m^2 + 2559552*m + 828288) * r ^ 3 * ρ ^ 4 + (438*m^8 + 10104*m^7 + 101340*m^6 + 577792*m^5 + 2050614*m^4 + 4644552*m^3 + 6564088*m^2 + 5298432*m + 1872000) * r ^ 4 * ρ ^ 3 + (274*m^8 + 6680*m^7 + 71140*m^6 + 432784*m^5 + 1646722*m^4 + 4016088*m^3 + 6133704*m^2 + 5364288*m + 2056320) * r ^ 5 * ρ ^ 2 + (22*m^8 + 840*m^7 + 12316*m^6 + 96224*m^5 + 449654*m^4 + 1304152*m^3 + 2310104*m^2 + 2295552*m + 982656) * r ^ 6 * ρ ^ 1 + (98*m^8 + 2600*m^7 + 30020*m^6 + 197104*m^5 + 805170*m^4 + 2096040*m^3 + 3396392*m^2 + 3132480*m + 1259136) * r ^ 7 * ρ ^ 0 := by
    rw [hρdef]; ring
  have hnn : 0 ≤ (2*m^8 + 40*m^7 + 340*m^6 + 1600*m^5 + 4546*m^4 + 7960*m^3 + 8360*m^2 + 4800*m + 1152) * r ^ 0 * ρ ^ 7 + (22*m^8 + 456*m^7 + 4044*m^6 + 20016*m^5 + 60390*m^4 + 113544*m^3 + 129656*m^2 + 81984*m + 21888) * r ^ 1 * ρ ^ 6 + (114*m^8 + 2456*m^7 + 22772*m^6 + 118624*m^5 + 379474*m^4 + 762696*m^3 + 939336*m^2 + 646848*m + 190080) * r ^ 2 * ρ ^ 5 + (310*m^8 + 6904*m^7 + 66508*m^6 + 362064*m^5 + 1218726*m^4 + 2598392*m^3 + 3428056*m^2 + 2559552*m + 828288) * r ^ 3 * ρ ^ 4 + (438*m^8 + 10104*m^7 + 101340*m^6 + 577792*m^5 + 2050614*m^4 + 4644552*m^3 + 6564088*m^2 + 5298432*m + 1872000) * r ^ 4 * ρ ^ 3 + (274*m^8 + 6680*m^7 + 71140*m^6 + 432784*m^5 + 1646722*m^4 + 4016088*m^3 + 6133704*m^2 + 5364288*m + 2056320) * r ^ 5 * ρ ^ 2 + (22*m^8 + 840*m^7 + 12316*m^6 + 96224*m^5 + 449654*m^4 + 1304152*m^3 + 2310104*m^2 + 2295552*m + 982656) * r ^ 6 * ρ ^ 1 + (98*m^8 + 2600*m^7 + 30020*m^6 + 197104*m^5 + 805170*m^4 + 2096040*m^3 + 3396392*m^2 + 3132480*m + 1259136) * r ^ 7 * ρ ^ 0 := by positivity
  rw [← hid] at hnn
  exact (mul_nonneg_iff_of_pos_left hT).mp hnn

lemma bracket_nonneg (c r s q K : ℝ)
    (hE : 0 ≤ 2 * q * (r ^ 4 + q) - (2 * c + r) * r ^ 3 * K) (hc2 : 2 * c * s ≤ r)
    (hK : 0 ≤ r ^ 3 * K) : 0 ≤ q * (r ^ 4 + q) - (1 + s) * c * r ^ 3 * K := by
  have h := mul_le_mul_of_nonneg_right hc2 hK
  have e : q * (r ^ 4 + q) - (1 + s) * c * r ^ 3 * K =
      (2 * q * (r ^ 4 + q) - (2 * c + r) * r ^ 3 * K) / 2 + (r * (r ^ 3 * K) - 2 * c * s * (r ^ 3 * K)) / 2 := by
    ring
  rw [e]
  have : 0 ≤ r * (r ^ 3 * K) - 2 * c * s * (r ^ 3 * K) := by linarith
  positivity

lemma xSum_update {C : ℕ} (z : ℕ → ℝ) (t : ℝ) : xSum C (Function.update z 1 t) = xSum C z := by
  unfold xSum
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_Icc] at hk
  unfold zExt
  split_ifs
  · rw [Function.update_of_ne (by omega)]
  · rfl

lemma ySum_update {C : ℕ} (z : ℕ → ℝ) (t : ℝ) : ySum C (Function.update z 1 t) = ySum C z := by
  unfold ySum
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_Icc] at hk
  unfold zExt
  split_ifs
  · rw [Function.update_of_ne (by omega)]
  · rfl

lemma Rt_update {C : ℕ} (hC : 4 ≤ C) (z : ℕ → ℝ) (t : ℝ) :
    Rt C (Function.update z 1 t) =
      (t + xSum C z) * (a C 1 * ((C : ℝ) * t + ySum C z) ^ 3 +
        a C 2 * ((C : ℝ) * t + ySum C z) ^ 2 * xSum C z +
        a C 3 * ((C : ℝ) * t + ySum C z) * xSum C z ^ 2 + a C 4 * xSum C z ^ 3) /
      (((C : ℝ) * t + ySum C z) ^ 4 + a C 1 * ((C : ℝ) * t + ySum C z) ^ 3 * xSum C z +
        a C 2 * ((C : ℝ) * t + ySum C z) ^ 2 * xSum C z ^ 2 +
        a C 3 * ((C : ℝ) * t + ySum C z) * xSum C z ^ 3 + a C 4 * xSum C z ^ 4) := by
  unfold Rt
  rw [N0_eq (by omega), u_eq (by omega), xSum_update, ySum_update, Function.update_self, Icc14,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, a_zero]
  norm_num
  ring

end SolSRGComb

open SolSRGComb StaticReusable.Guarantee in
theorem solution {C : ℕ} (hC : 4 ≤ C) (z : ℕ → ℝ) (hz : ∀ k ∈ Finset.Icc 1 C, 0 ≤ z k)
    (hy : StaticReusable.Guarantee.a C 1 * z 1 ≤ StaticReusable.Guarantee.ySum C z) :
    ∃ d : ℝ, HasDerivAt (fun t : ℝ => StaticReusable.Guarantee.Rt C (Function.update z 1 t)) d (z 1) ∧
      0 ≤ d := by
  have hx := x_pos (by omega) hz
  have ha1 : a C 1 = C := by unfold a; simp
  set x := xSum C z with hxdef
  set y := ySum C z with hydef
  set c : ℝ := (C : ℝ) with hcdef
  set α1 := a C 1
  set α2 := a C 2
  set α3 := a C 3
  set α4 := a C 4
  have hc4 : (4 : ℝ) ≤ c := by rw [hcdef]; exact_mod_cast hC
  have hα : α1 = c ∧ α2 = c * (c - 1) ∧ α3 = c * (c - 1) * (c - 2) ∧
      α4 = c * (c - 1) * (c - 2) * (c - 3) := by
    have h1 : a C 1 = C := ha1
    have h2 : a C 2 = C * (C - 1) := by rw [a_succ C 1 (by omega), h1]; push_cast; ring
    have h3 : a C 3 = C * (C - 1) * (C - 2) := by rw [a_succ C 2 (by omega), h2]; push_cast; ring
    have h4 : a C 4 = C * (C - 1) * (C - 2) * (C - 3) := by
      rw [a_succ C 3 (by omega), h3]; push_cast; ring
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨e1, e2, e3, e4⟩ := hα
  have hfun : (fun t : ℝ => Rt C (Function.update z 1 t)) = fun t =>
      ((t + x) * (α1 * (c * t + y) ^ 3 + α2 * (c * t + y) ^ 2 * x + α3 * (c * t + y) * x ^ 2 +
        α4 * x ^ 3)) /
      ((c * t + y) ^ 4 + α1 * (c * t + y) ^ 3 * x + α2 * (c * t + y) ^ 2 * x ^ 2 +
        α3 * (c * t + y) * x ^ 3 + α4 * x ^ 4) := by
    funext t; exact Rt_update hC z t
  rw [hfun]
  set t0 := z 1 with ht0
  have hz1 : 0 ≤ t0 := hz 1 (by simp; omega)
  have hy0 : 0 ≤ y := by
    have := u_eq (C := C) (by omega) z
    nlinarith [u_nonneg hz, mul_nonneg (show (0:ℝ) ≤ C by positivity) hz1, hy]
  have hL : HasDerivAt (fun t : ℝ => c * t + y) c t0 := by
    have := ((hasDerivAt_id t0).const_mul c).add_const y
    simpa using this
  set U := c * t0 + y with hU
  have hP : HasDerivAt (fun t : ℝ => (t + x) * (α1 * (c * t + y) ^ 3 + α2 * (c * t + y) ^ 2 * x +
      α3 * (c * t + y) * x ^ 2 + α4 * x ^ 3))
      ((α1 * U ^ 3 + α2 * U ^ 2 * x + α3 * U * x ^ 2 + α4 * x ^ 3) +
        (t0 + x) * (c * (3 * α1 * U ^ 2 + 2 * α2 * U * x + α3 * x ^ 2))) t0 := by
    have h1 : HasDerivAt (fun t : ℝ => t + x) 1 t0 := (hasDerivAt_id t0).add_const x
    have h2 := ((((hL.fun_pow 3).const_mul α1).fun_add (((hL.fun_pow 2).const_mul α2).mul_const x)).fun_add
      ((hL.const_mul α3).mul_const (x ^ 2))).add_const (α4 * x ^ 3)
    have := h1.fun_mul h2
    refine this.congr_deriv ?_
    simp only [hU, show (3:ℕ) - 1 = 2 from rfl, show (2:ℕ) - 1 = 1 from rfl,
      show (4:ℕ) - 1 = 3 from rfl, pow_one, Nat.cast_ofNat]
    ring
  have hQ : HasDerivAt (fun t : ℝ => (c * t + y) ^ 4 + α1 * (c * t + y) ^ 3 * x +
      α2 * (c * t + y) ^ 2 * x ^ 2 + α3 * (c * t + y) * x ^ 3 + α4 * x ^ 4)
      (c * (4 * U ^ 3 + 3 * α1 * U ^ 2 * x + 2 * α2 * U * x ^ 2 + α3 * x ^ 3)) t0 := by
    have := (((((hL.fun_pow 4).fun_add (((hL.fun_pow 3).const_mul α1).mul_const x)).fun_add
      (((hL.fun_pow 2).const_mul α2).mul_const (x ^ 2))).fun_add
      ((hL.const_mul α3).mul_const (x ^ 3))).add_const (α4 * x ^ 4))
    refine this.congr_deriv ?_
    simp only [hU, show (3:ℕ) - 1 = 2 from rfl, show (2:ℕ) - 1 = 1 from rfl,
      show (4:ℕ) - 1 = 3 from rfl, pow_one, Nat.cast_ofNat]
    ring
  have hU0 : 0 ≤ U := by positivity
  have hα4 : 0 < α4 := by unfold α4 a; exact_mod_cast Nat.descFactorial_pos.2 hC
  have hα1 : 0 ≤ α1 := a_nonneg C 1
  have hα2 : 0 ≤ α2 := a_nonneg C 2
  have hα3 : 0 ≤ α3 := a_nonneg C 3
  have hQpos : 0 < U ^ 4 + α1 * U ^ 3 * x + α2 * U ^ 2 * x ^ 2 + α3 * U * x ^ 3 + α4 * x ^ 4 := by
    positivity
  have hD := hP.div hQ hQpos.ne'
  refine ⟨_, hD, ?_⟩
  apply div_nonneg _ (sq_nonneg _)
  -- normalize
  set r := U / x with hr
  set s := t0 / x with hs
  have hUr : U = r * x := by rw [hr]; field_simp
  have hts : t0 = s * x := by rw [hs]; field_simp
  have hr0 : 0 ≤ r := div_nonneg hU0 hx.le
  have hs0 : 0 ≤ s := div_nonneg hz1 hx.le
  -- constraints
  have hyl := y_le (C := C) (by omega) hz
  rw [← hxdef, ← hydef] at hyl
  rw [ha1] at hy
  have hc2 : 2 * c * s ≤ r := by
    rw [hr, hs, le_div_iff₀ hx, hU]
    rw [mul_assoc, div_mul_cancel₀ _ hx.ne']
    linarith
  have hrT : r ≤ 2 * c - 2 := by
    have h1 : r ≤ c * s + (c - 1) := by
      rw [hr, hs, div_le_iff₀ hx, hU, add_mul, mul_assoc, div_mul_cancel₀ _ hx.ne']
      linarith
    linarith
  -- the bracket
  set q := α1 * r ^ 3 + α2 * r ^ 2 + α3 * r + α4 with hq
  set K := α1 * r ^ 3 + 2 * α2 * r ^ 2 + 3 * α3 * r + 4 * α4 with hK
  have hqn : 0 ≤ q := by positivity
  have hKn : 0 ≤ K := by positivity
  have hnum : ((α1 * U ^ 3 + α2 * U ^ 2 * x + α3 * U * x ^ 2 + α4 * x ^ 3) +
        (t0 + x) * (c * (3 * α1 * U ^ 2 + 2 * α2 * U * x + α3 * x ^ 2))) *
        (U ^ 4 + α1 * U ^ 3 * x + α2 * U ^ 2 * x ^ 2 + α3 * U * x ^ 3 + α4 * x ^ 4) -
      ((t0 + x) * (α1 * U ^ 3 + α2 * U ^ 2 * x + α3 * U * x ^ 2 + α4 * x ^ 3)) *
        (c * (4 * U ^ 3 + 3 * α1 * U ^ 2 * x + 2 * α2 * U * x ^ 2 + α3 * x ^ 3)) =
      x ^ 7 * (q * (r ^ 4 + q) - (1 + s) * c * r ^ 3 * K) := by
    rw [hUr, hts, hq, hK]; ring
  rw [hnum]
  apply mul_nonneg (by positivity)
  have hE := keyE (c - 4) r (by linarith) hr0 (by linarith)
  have hcm : c - 4 + 4 = c := by ring
  have hcm3 : c - 4 + 3 = c - 1 := by ring
  have hcm2 : c - 4 + 2 = c - 2 := by ring
  have hcm1 : c - 4 + 1 = c - 3 := by ring
  rw [hcm, hcm3, hcm2, hcm1] at hE
  have hq' : q = c * r ^ 3 + c * (c - 1) * r ^ 2 + c * (c - 1) * (c - 2) * r +
      c * (c - 1) * (c - 2) * (c - 3) := by rw [hq, e1, e2, e3, e4]
  have hK' : K = c * r ^ 3 + 2 * (c * (c - 1)) * r ^ 2 + 3 * (c * (c - 1) * (c - 2)) * r +
      4 * (c * (c - 1) * (c - 2) * (c - 3)) := by rw [hK, e1, e2, e3, e4]
  have hE' : 0 ≤ 2 * q * (r ^ 4 + q) - (2 * c + r) * r ^ 3 * K := by
    rw [hq', hK']; linarith [hE]
  have hr3K : 0 ≤ r ^ 3 * K := by positivity
  exact bracket_nonneg c r s q K hE' hc2 hr3K

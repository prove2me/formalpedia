-- Prove2me | solution 1 for RamanujanNotebooks.entry_16_19
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T03:11:25.673889+00:00
-- url     : https://prove2.me/submissions/f38e23f7-eaa0-4ed6-8323-68a3afa85b63

import Mathlib
import Definitions.Def_RamanujanNotebooks_shared_qPochInf
import Definitions.Def_RamanujanNotebooks_shared_ramanujanTheta

open Finset Filter Topology



namespace JTAux

/-- Gaussian binomial via q-Pascal. -/
def G (q : ℂ) : ℕ → ℕ → ℂ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | N + 1, m + 1 => G q N m + q ^ (m + 1) * G q N (m + 1)

def P (q : ℂ) (m : ℕ) : ℂ := ∏ k ∈ range m, (1 - q ^ (k + 1))

def T (m : ℕ) : ℕ := ∑ i ∈ range m, i

theorem T_zero : T 0 = 0 := rfl

theorem G_zero_right (q : ℂ) (N : ℕ) : G q N 0 = 1 := by cases N <;> rfl

theorem G_eq_zero (q : ℂ) : ∀ N m, N < m → G q N m = 0
  | 0, m + 1, _ => rfl
  | N + 1, m + 1, h => by
    simp only [G]
    rw [G_eq_zero q N m (by omega), G_eq_zero q N (m + 1) (by omega)]; ring

theorem qbinom (q : ℂ) : ∀ (N : ℕ) (x : ℂ),
    ∏ k ∈ range N, (1 + x * q ^ k) = ∑ m ∈ range (N + 1), G q N m * q ^ T m * x ^ m
  | 0, x => by simp [G, T]
  | N + 1, x => by
    rw [prod_range_succ', pow_zero, mul_one]
    have h1 : ∏ k ∈ range N, (1 + x * q ^ (k + 1)) = ∏ k ∈ range N, (1 + (x * q) * q ^ k) := by
      refine prod_congr rfl fun k _ => by ring
    rw [h1, qbinom q N (x * q)]
    have hT : ∀ m, T (m + 1) = T m + m := fun m => by simp [T, sum_range_succ]
    have hL : ∀ m, G q N m * q ^ T m * (x * q) ^ m = G q N m * q ^ (T m + m) * x ^ m := by
      intro m; rw [mul_pow, pow_add]; ring
    simp only [hL]
    rw [sum_range_succ' _ (N + 1)]
    have hR : ∀ m, G q (N + 1) (m + 1) * q ^ T (m + 1) * x ^ (m + 1) =
        G q N m * q ^ (T m + m) * x ^ (m + 1) +
          q ^ (m + 1) * G q N (m + 1) * q ^ (T m + m) * x ^ (m + 1) := by
      intro m; simp only [G, hT]; ring
    simp only [hR, sum_add_distrib, G_zero_right, T_zero, pow_zero, mul_one]
    have h2 : ∑ m ∈ range (N + 1), G q N m * q ^ (T m + m) * x ^ m =
        ∑ m ∈ range (N + 1), q ^ (m + 1) * G q N (m + 1) * q ^ (T m + m) * x ^ (m + 1) + 1 := by
      rw [sum_range_succ' _ N, sum_range_succ _ N, G_eq_zero q N (N + 1) (by omega)]
      simp only [G_zero_right, T_zero, pow_zero, mul_one, zero_mul, mul_zero, add_zero]
      congr 1
      refine sum_congr rfl fun m _ => ?_
      rw [hT, pow_add, pow_add, pow_add]; ring
    rw [mul_add, mul_one, sum_mul, h2]
    have h3 : ∀ m ∈ range (N + 1), G q N m * q ^ (T m + m) * x ^ m * x =
        G q N m * q ^ (T m + m) * x ^ (m + 1) := fun m _ => by ring
    rw [sum_congr rfl h3]; ring

end JTAux



namespace JTAux

theorem P_zero (q : ℂ) : P q 0 = 1 := by simp [P]

theorem P_succ (q : ℂ) (k : ℕ) : P q (k + 1) = P q k * (1 - q ^ (k + 1)) := by
  simp [P, prod_range_succ]

theorem G_formula (q : ℂ) : ∀ N m, m ≤ N → G q N m * P q m * P q (N - m) = P q N
  | N, 0, _ => by simp [G_zero_right, P_zero]
  | 0, m + 1, h => absurd h (by omega)
  | N + 1, m + 1, h => by
    have h1 := G_formula q N m (by omega)
    have t2 : q ^ (m + 1) * G q N (m + 1) * P q (m + 1) * P q (N - m) =
        q ^ (m + 1) * P q N * (1 - q ^ (N - m)) := by
      by_cases hm : m + 1 ≤ N
      · have h2 := G_formula q N (m + 1) hm
        have : N - m = (N - (m + 1)) + 1 := by omega
        have hP : P q (N - m) = P q (N - (m + 1)) * (1 - q ^ (N - m)) := by
          conv_lhs => rw [this]
          rw [P_succ, ← this]
        rw [hP, ← h2]; ring
      · have hmN : m = N := by omega
        subst hmN
        rw [G_eq_zero q m (m + 1) (by omega)]; simp
    have e : N + 1 - (m + 1) = N - m := by omega
    simp only [G]
    rw [e, P_succ, P_succ]
    have : (G q N m + q ^ (m + 1) * G q N (m + 1)) * (P q m * (1 - q ^ (m + 1))) * P q (N - m) =
        (G q N m * P q m * P q (N - m)) * (1 - q ^ (m + 1)) +
          q ^ (m + 1) * G q N (m + 1) * (P q m * (1 - q ^ (m + 1))) * P q (N - m) := by ring
    rw [this, h1, ← P_succ, t2]
    have : q ^ (m + 1) * q ^ (N - m) = q ^ (N + 1) := by rw [← pow_add]; congr 1; omega
    linear_combination (-P q N) * this

theorem exp_le_one_sub (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) : Real.exp (-(x / (1 - x))) ≤ 1 - x := by
  have h2 : 0 < 1 - x := by linarith
  have := Real.add_one_le_exp (x / (1 - x))
  have h3 : x / (1 - x) + 1 = 1 / (1 - x) := by field_simp; ring
  rw [h3] at this
  rw [Real.exp_neg]
  calc (Real.exp (x / (1 - x)))⁻¹ ≤ (1 / (1 - x))⁻¹ := by
        apply inv_anti₀ (by positivity) this
    _ = 1 - x := by simp

theorem geom_le (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) (m : ℕ) :
    ∑ k ∈ range m, r ^ (k + 1) ≤ r / (1 - r) := by
  have : ∑ k ∈ range m, r ^ (k + 1) = r * ∑ k ∈ range m, r ^ k := by
    rw [mul_sum]; refine sum_congr rfl fun k _ => by ring
  rw [this, div_eq_mul_one_div]
  apply mul_le_mul_of_nonneg_left _ h0
  rw [one_div, ← tsum_geometric_of_lt_one h0 h1]
  exact (summable_geometric_of_lt_one h0 h1).sum_le_tsum _ (fun k _ => pow_nonneg h0 k)

theorem P_lower (q : ℂ) (hq : ‖q‖ < 1) (m : ℕ) :
    Real.exp (-(‖q‖ / (1 - ‖q‖) ^ 2)) ≤ ‖P q m‖ := by
  set r := ‖q‖
  have hr0 : 0 ≤ r := norm_nonneg q
  have h1r : 0 < 1 - r := by linarith
  rw [P, norm_prod]
  calc Real.exp (-(r / (1 - r) ^ 2)) ≤ Real.exp (-(∑ k ∈ range m, r ^ (k + 1)) / (1 - r)) := by
        apply Real.exp_le_exp.mpr
        rw [neg_div, neg_le_neg_iff, pow_two, ← div_div]
        exact div_le_div_of_nonneg_right (geom_le r hr0 hq m) h1r.le
    _ = ∏ k ∈ range m, Real.exp (-(r ^ (k + 1) / (1 - r))) := by
        rw [← Real.exp_sum]; congr 1; rw [neg_div, sum_div, ← sum_neg_distrib]
    _ ≤ ∏ k ∈ range m, ‖1 - q ^ (k + 1)‖ := by
        apply prod_le_prod (fun k _ => (Real.exp_pos _).le)
        intro k _
        have hx0 : 0 ≤ r ^ (k + 1) := pow_nonneg hr0 _
        have hxr : r ^ (k + 1) ≤ r := pow_le_of_le_one hr0 hq.le (by omega)
        have hx1 : r ^ (k + 1) < 1 := lt_of_le_of_lt hxr hq
        calc Real.exp (-(r ^ (k + 1) / (1 - r))) ≤ Real.exp (-(r ^ (k + 1) / (1 - r ^ (k + 1)))) := by
              apply Real.exp_le_exp.mpr
              rw [neg_le_neg_iff]
              exact div_le_div_of_nonneg_left hx0 (by linarith) (by linarith)
          _ ≤ 1 - r ^ (k + 1) := exp_le_one_sub _ hx0 hx1
          _ ≤ ‖1 - q ^ (k + 1)‖ := by
              have := norm_sub_norm_le (1 : ℂ) (q ^ (k + 1))
              rw [norm_one, norm_pow] at this
              exact this

theorem P_upper (q : ℂ) (hq : ‖q‖ < 1) (m : ℕ) : ‖P q m‖ ≤ Real.exp (‖q‖ / (1 - ‖q‖)) := by
  set r := ‖q‖
  have hr0 : 0 ≤ r := norm_nonneg q
  rw [P, norm_prod]
  calc ∏ k ∈ range m, ‖1 - q ^ (k + 1)‖ ≤ ∏ k ∈ range m, Real.exp (r ^ (k + 1)) := by
        apply prod_le_prod (fun k _ => norm_nonneg _)
        intro k _
        calc ‖1 - q ^ (k + 1)‖ ≤ ‖(1 : ℂ)‖ + ‖q ^ (k + 1)‖ := norm_sub_le _ _
          _ = r ^ (k + 1) + 1 := by rw [norm_one, norm_pow]; ring
          _ ≤ Real.exp (r ^ (k + 1)) := Real.add_one_le_exp _
    _ = Real.exp (∑ k ∈ range m, r ^ (k + 1)) := by rw [Real.exp_sum]
    _ ≤ Real.exp (r / (1 - r)) := Real.exp_le_exp.mpr (geom_le r hr0 hq m)

theorem P_ne_zero (q : ℂ) (hq : ‖q‖ < 1) (m : ℕ) : P q m ≠ 0 := by
  intro h
  have := P_lower q hq m
  rw [h, norm_zero] at this
  exact absurd this (not_le.mpr (Real.exp_pos _))

theorem G_eq_div (q : ℂ) (hq : ‖q‖ < 1) (N m : ℕ) (h : m ≤ N) :
    G q N m = P q N / (P q m * P q (N - m)) := by
  rw [eq_div_iff (mul_ne_zero (P_ne_zero q hq m) (P_ne_zero q hq _)), ← mul_assoc,
    G_formula q N m h]

theorem G_bound (q : ℂ) (hq : ‖q‖ < 1) (N m : ℕ) :
    ‖G q N m‖ ≤ Real.exp (‖q‖ / (1 - ‖q‖)) / (Real.exp (-(‖q‖ / (1 - ‖q‖) ^ 2))) ^ 2 := by
  by_cases h : m ≤ N
  · rw [G_eq_div q hq N m h, norm_div, norm_mul, pow_two]
    apply div_le_div₀ (by positivity) (P_upper q hq N) (by positivity)
    exact mul_le_mul (P_lower q hq m) (P_lower q hq _) (by positivity) (norm_nonneg _)
  · rw [G_eq_zero q N m (by omega), norm_zero]; positivity

/-- `(x; q)_∞` as limit of partial products. -/
theorem poch_tendsto (x q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun n => ∏ k ∈ range n, (1 - x * q ^ k)) atTop (𝓝 (∏' k : ℕ, (1 - x * q ^ k))) := by
  have hs : Summable fun k : ℕ => ‖-(x * q ^ k)‖ := by
    simp only [norm_neg, norm_mul, norm_pow]
    exact (summable_geometric_of_lt_one (norm_nonneg _) hq).mul_left _
  have hm := multipliable_one_add_of_summable hs
  simp only [← sub_eq_add_neg] at hm
  exact hm.hasProd.tendsto_prod_nat

theorem P_tendsto (q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (P q) atTop (𝓝 (∏' k : ℕ, (1 - q * q ^ k))) := by
  have := poch_tendsto q q hq
  refine this.congr fun n => ?_
  simp only [P]
  refine prod_congr rfl fun k _ => by ring

theorem Pinf_ne_zero (q : ℂ) (hq : ‖q‖ < 1) : (∏' k : ℕ, (1 - q * q ^ k)) ≠ 0 := by
  intro h
  have ht := (P_tendsto q hq).norm
  rw [h, norm_zero] at ht
  have := ge_of_tendsto ht (Eventually.of_forall fun m => P_lower q hq m)
  exact absurd this (not_le.mpr (Real.exp_pos _))

end JTAux



namespace JTAux

def c (a b : ℂ) (j : ℤ) : ℂ := a ^ (j * (j + 1) / 2).toNat * b ^ (j * (j - 1) / 2).toNat

theorem T_two (n : ℕ) : (T n : ℤ) * 2 = n * ((n : ℤ) - 1) := by
  have := Finset.sum_range_id_mul_two n
  rw [T]
  rcases n with _ | n
  · simp
  · simp only [Nat.add_sub_cancel] at this
    have h : ((∑ i ∈ range (n + 1), i : ℕ) : ℤ) * 2 = ((n + 1) * n : ℕ) := by
      rw [← this]; push_cast; ring
    rw [h]; push_cast; ring

theorem alpha_eq (n m : ℕ) :
    (((m : ℤ) - n) * ((m : ℤ) - n + 1) / 2).toNat + n * m = T n + T m + m := by
  have h1 := T_two n
  have h2 := T_two m
  have hX : ((m : ℤ) - n) * ((m : ℤ) - n + 1) = 2 * ((T n : ℤ) + T m + m - n * m) := by
    linear_combination (-1 : ℤ) * h1 - h2
  rw [hX, Int.mul_ediv_cancel_left _ two_ne_zero]
  have hnn : 0 ≤ (T n : ℤ) + T m + m - n * m := by
    have : 0 ≤ ((m : ℤ) - n) * ((m : ℤ) - n + 1) := by
      rcases le_or_gt 0 ((m : ℤ) - n) with h | h
      · positivity
      · nlinarith
    linarith
  zify [hnn]
  rw [Int.toNat_of_nonneg hnn]; ring

theorem beta_eq (n m : ℕ) :
    (((m : ℤ) - n) * ((m : ℤ) - n - 1) / 2).toNat + n * m = n + T n + T m := by
  have h1 := T_two n
  have h2 := T_two m
  have hX : ((m : ℤ) - n) * ((m : ℤ) - n - 1) = 2 * ((n : ℤ) + T n + T m - n * m) := by
    linear_combination (-1 : ℤ) * h1 - h2
  rw [hX, Int.mul_ediv_cancel_left _ two_ne_zero]
  have hnn : 0 ≤ (n : ℤ) + T n + T m - n * m := by
    have : 0 ≤ ((m : ℤ) - n) * ((m : ℤ) - n - 1) := by
      rcases le_or_gt ((m : ℤ) - n) 0 with h | h
      · nlinarith
      · nlinarith
    linarith
  zify [hnn]
  rw [Int.toNat_of_nonneg hnn]; ring

theorem finite_jtp (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (n : ℕ) :
    (∏ k ∈ range n, (1 + a * (a * b) ^ k)) * (∏ k ∈ range n, (1 + b * (a * b) ^ k)) =
      ∑ m ∈ range (2 * n + 1), G (a * b) (2 * n) m * c a b ((m : ℤ) - n) := by
  set q := a * b with hq_def
  have hq : q ≠ 0 := mul_ne_zero ha hb
  -- step (i)
  have s1 : ∏ k ∈ range n, (1 + b * q ^ k) =
      b ^ n * q ^ T n * ∏ k ∈ range n, (1 + a * (q ^ (k + 1))⁻¹) := by
    have : ∀ k ∈ range n, 1 + b * q ^ k = (b * q ^ k) * (1 + a * (q ^ (k + 1))⁻¹) := by
      intro k _
      rw [pow_succ]
      field_simp
      rw [hq_def]; ring
    rw [prod_congr rfl this, prod_mul_distrib, prod_mul_distrib, prod_const, card_range,
      prod_pow_eq_pow_sum, T]
  -- step (ii)
  set x := a * (q ^ n)⁻¹
  have s2 : (∏ k ∈ range n, (1 + a * (q ^ (k + 1))⁻¹)) * ∏ k ∈ range n, (1 + a * q ^ k) =
      ∏ k ∈ range (2 * n), (1 + x * q ^ k) := by
    rw [two_mul, prod_range_add, ← prod_range_reflect (fun k => 1 + x * q ^ k) n]
    congr 1
    · refine prod_congr rfl fun k hk => ?_
      rw [mem_range] at hk
      simp only [x]
      have : q ^ n = q ^ (n - 1 - k) * q ^ (k + 1) := by rw [← pow_add]; congr 1; omega
      rw [this]
      field_simp
    · refine prod_congr rfl fun k _ => ?_
      simp only [x]
      rw [pow_add]
      field_simp
  rw [s1]
  have e : (∏ k ∈ range n, (1 + a * q ^ k)) *
      (b ^ n * q ^ T n * ∏ k ∈ range n, (1 + a * (q ^ (k + 1))⁻¹)) =
      b ^ n * q ^ T n * ((∏ k ∈ range n, (1 + a * (q ^ (k + 1))⁻¹)) *
        ∏ k ∈ range n, (1 + a * q ^ k)) := by ring
  rw [e, s2, qbinom q (2 * n) x, mul_sum]
  refine sum_congr rfl fun m _ => ?_
  have hx : x ^ m = a ^ m / q ^ (n * m) := by
    simp only [x]; rw [mul_pow, inv_pow, ← pow_mul]; ring
  rw [hx]
  have key : b ^ n * q ^ T n * q ^ T m * a ^ m = c a b ((m : ℤ) - n) * q ^ (n * m) := by
    simp only [c]
    rw [hq_def, mul_pow, mul_pow, mul_pow]
    have e1 := alpha_eq n m
    have e2 := beta_eq n m
    calc b ^ n * (a ^ T n * b ^ T n) * (a ^ T m * b ^ T m) * a ^ m
        = a ^ (T n + T m + m) * b ^ (n + T n + T m) := by ring
      _ = _ := by rw [← e1, ← e2, pow_add, pow_add]; ring
  have hqnm : q ^ (n * m) ≠ 0 := pow_ne_zero _ hq
  field_simp
  linear_combination G q (2 * n) m * key

end JTAux



namespace JTAux

theorem summ_aux (s r : ℝ) (hs : 0 < s) (hr0 : 0 < r) (hr : r < 1) :
    Summable fun n : ℕ => s ^ n * r ^ T n := by
  apply summable_of_ratio_test_tendsto_lt_one (l := 0) zero_lt_one
  · exact Eventually.of_forall fun n => by positivity
  · have hT : ∀ m, T (m + 1) = T m + m := fun m => by simp [T, sum_range_succ]
    have : (fun n : ℕ => ‖s ^ (n + 1) * r ^ T (n + 1)‖ / ‖s ^ n * r ^ T n‖) =
        fun n => s * r ^ n := by
      funext n
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), hT, pow_succ,
        pow_add]
      field_simp
    rw [this]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr).const_mul s

theorem c_nat (a b : ℂ) (n : ℕ) : c a b n = a ^ n * (a * b) ^ T n := by
  have e1 := alpha_eq 0 n
  have e2 := beta_eq 0 n
  simp only [Nat.cast_zero, sub_zero, zero_mul, add_zero, T_zero, zero_add] at e1 e2
  simp only [c, e1, e2, mul_pow, pow_add]; ring

theorem c_neg (a b : ℂ) (n : ℕ) : c a b (-((n : ℤ) + 1)) = b ^ (n + 1) * (a * b) ^ T (n + 1) := by
  have e1 := alpha_eq (n + 1) 0
  have e2 := beta_eq (n + 1) 0
  simp only [Nat.cast_zero, zero_sub, mul_zero, add_zero, T_zero, Nat.cast_add, Nat.cast_one] at e1 e2
  simp only [c, e1, e2, mul_pow, pow_add]; ring

theorem summ_c (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hq : ‖a * b‖ < 1) :
    Summable fun j : ℤ => ‖c a b j‖ := by
  have hq0 : 0 < ‖a * b‖ := norm_pos_iff.mpr (mul_ne_zero ha hb)
  apply Summable.of_nat_of_neg_add_one
  · refine (summ_aux ‖a‖ ‖a * b‖ (norm_pos_iff.mpr ha) hq0 hq).congr fun n => ?_
    simp only [c_nat, norm_mul, norm_pow]
  · have := (summ_aux ‖b‖ ‖a * b‖ (norm_pos_iff.mpr hb) hq0 hq).comp_injective
      (add_left_injective 1)
    refine this.congr fun n => ?_
    simp only [Function.comp, c_neg, norm_mul, norm_pow]

theorem tendsto_aux (j : ℤ) : Tendsto (fun n : ℕ => (j + n).toNat) atTop atTop :=
  tendsto_atTop_atTop.mpr fun b => ⟨b + j.natAbs, fun n hn => by omega⟩

theorem tendsto_aux2 (j : ℤ) : Tendsto (fun n : ℕ => 2 * n - (j + n).toNat) atTop atTop :=
  tendsto_atTop_atTop.mpr fun b => ⟨b + j.natAbs, fun n hn => by omega⟩

theorem tendsto_aux3 : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
  tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn => by omega⟩

theorem jtp_main (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hq : ‖a * b‖ < 1) :
    ∑' j : ℤ, c a b j = (∏' k : ℕ, (1 - (-a) * (a * b) ^ k)) * (∏' k : ℕ, (1 - (-b) * (a * b) ^ k)) *
      ∏' k : ℕ, (1 - (a * b) * (a * b) ^ k) := by
  set q := a * b with hq_def
  set Pinf := ∏' k : ℕ, (1 - q * q ^ k)
  have hPinf := Pinf_ne_zero q hq
  set B := Real.exp (‖q‖ / (1 - ‖q‖)) / (Real.exp (-(‖q‖ / (1 - ‖q‖) ^ 2))) ^ 2
  let F : ℕ → ℤ → ℂ := fun n j =>
    if -(n : ℤ) ≤ j ∧ j ≤ n then G q (2 * n) (j + n).toNat * c a b j else 0
  -- (1) finite sums
  have hF : ∀ n, ∑' j, F n j =
      (∏ k ∈ range n, (1 + a * q ^ k)) * (∏ k ∈ range n, (1 + b * q ^ k)) := by
    intro n
    rw [finite_jtp a b ha hb n]
    set s := (range (2 * n + 1)).image (fun m : ℕ => (m : ℤ) - n)
    rw [tsum_eq_sum (s := s)]
    · rw [sum_image]
      · refine sum_congr rfl fun m hm => ?_
        rw [mem_range] at hm
        simp only [F]
        rw [if_pos ⟨by omega, by omega⟩]
        congr 2; omega
      · intro x _ y _ h; simpa using h
    · intro j hj
      simp only [F]
      rw [if_neg]
      intro h
      apply hj
      rw [mem_image]
      exact ⟨(j + n).toNat, mem_range.mpr (by omega), by omega⟩
  -- (2) Tannery
  have hT : Tendsto (fun n => ∑' j, F n j) atTop (𝓝 (∑' j, c a b j / Pinf)) := by
    apply tendsto_tsum_of_dominated_convergence (bound := fun j => B * ‖c a b j‖)
    · exact (summ_c a b ha hb hq).mul_left B
    · intro j
      have h1 : Tendsto (fun n : ℕ => P q (2 * n) / (P q (j + n).toNat * P q (2 * n - (j + n).toNat))
          * c a b j) atTop (𝓝 (Pinf / (Pinf * Pinf) * c a b j)) := by
        refine Tendsto.mul_const _ (Tendsto.div ?_ (Tendsto.mul ?_ ?_) (mul_ne_zero hPinf hPinf))
        · exact (P_tendsto q hq).comp tendsto_aux3
        · exact (P_tendsto q hq).comp (tendsto_aux j)
        · exact (P_tendsto q hq).comp (tendsto_aux2 j)
      have h2 : Pinf / (Pinf * Pinf) * c a b j = c a b j / Pinf := by field_simp
      rw [← h2]
      refine h1.congr' ?_
      rw [EventuallyEq, eventually_atTop]
      refine ⟨j.natAbs, fun n hn => ?_⟩
      simp only [F]
      rw [if_pos ⟨by omega, by omega⟩, G_eq_div q hq _ _ (by omega)]
    · refine Eventually.of_forall fun n j => ?_
      simp only [F]
      split_ifs
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (G_bound q hq _ _) (norm_nonneg _)
      · rw [norm_zero]; exact mul_nonneg (by positivity) (norm_nonneg _)
  -- (3) products
  have hL : Tendsto (fun n => (∏ k ∈ range n, (1 + a * q ^ k)) * (∏ k ∈ range n, (1 + b * q ^ k)))
      atTop (𝓝 ((∏' k : ℕ, (1 - (-a) * q ^ k)) * (∏' k : ℕ, (1 - (-b) * q ^ k)))) := by
    refine Tendsto.mul ((poch_tendsto (-a) q hq).congr fun n => ?_)
      ((poch_tendsto (-b) q hq).congr fun n => ?_)
    · refine prod_congr rfl fun k _ => by ring
    · refine prod_congr rfl fun k _ => by ring
  have hU := tendsto_nhds_unique (hT.congr hF) hL
  rw [tsum_div_const] at hU
  rw [← hU, div_mul_cancel₀ _ hPinf]

end JTAux



namespace JTAux

theorem tri_ne (j : ℤ) (h0 : j ≠ 0) (h1 : j ≠ -1) : (j * (j + 1) / 2).toNat ≠ 0 := by
  have hp : 2 ≤ j * (j + 1) := by
    rcases lt_or_gt_of_ne h0 with h | h
    · have : j ≤ -2 := by omega
      nlinarith
    · nlinarith
  generalize j * (j + 1) = p at hp
  omega

theorem tri_ne' (j : ℤ) (h0 : j ≠ 0) (h1 : j ≠ 1) : (j * (j - 1) / 2).toNat ≠ 0 := by
  have hp : 2 ≤ j * (j - 1) := by
    rcases lt_or_gt_of_ne h0 with h | h
    · nlinarith
    · have : 2 ≤ j := by omega
      nlinarith
  generalize j * (j - 1) = p at hp
  omega

theorem poch_zero (x : ℂ) : (∏' k : ℕ, (1 - x * (0 : ℂ) ^ k)) = 1 - x := by
  rw [tprod_eq_prod (s := {0})]
  · simp
  · intro k hk
    rw [mem_singleton] at hk
    simp [zero_pow hk]

end JTAux

open RamanujanNotebooks in
theorem solution (a b : ℂ) (hab : ‖a * b‖ < 1) :
    ramanujanTheta a b = qPochInf (-a) (a * b) * qPochInf (-b) (a * b) * qPochInf (a * b) (a * b) := by
  by_cases ha : a = 0
  · subst ha
    simp only [zero_mul, qPochInf, JTAux.poch_zero, neg_zero, sub_zero, sub_neg_eq_add, mul_one, one_mul]
    rw [ramanujanTheta, tsum_eq_sum (s := {0, -1})]
    · rw [sum_pair (by norm_num)]
      norm_num
    · intro j hj
      simp only [mem_insert, mem_singleton, not_or] at hj
      rw [zero_pow (JTAux.tri_ne j hj.1 hj.2), zero_mul]
  by_cases hb : b = 0
  · subst hb
    simp only [mul_zero, qPochInf, JTAux.poch_zero, neg_zero, sub_zero, sub_neg_eq_add, mul_one]
    rw [ramanujanTheta, tsum_eq_sum (s := {0, 1})]
    · rw [sum_pair (by norm_num)]
      norm_num
    · intro j hj
      simp only [mem_insert, mem_singleton, not_or] at hj
      rw [zero_pow (JTAux.tri_ne' j hj.1 hj.2), mul_zero]
  exact JTAux.jtp_main a b ha hb hab

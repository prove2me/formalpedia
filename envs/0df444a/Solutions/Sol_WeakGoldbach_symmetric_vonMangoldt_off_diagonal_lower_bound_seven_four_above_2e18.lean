-- Prove2me | solution 1 for WeakGoldbach.symmetric_vonMangoldt_off_diagonal_lower_bound_seven_four_above_2e18
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-02T04:19:34.768484+00:00
-- url     : https://prove2.me/submissions/fc6d7e90-6070-4f9c-9f4c-30cce9073426

import Mathlib

namespace WGDisproof

open Finset

noncomputable def R (N : ℕ) : ℝ := 1 - 1 / (N : ℝ)

noncomputable def Lam (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n

lemma Lam_nonneg (n : ℕ) : 0 ≤ Lam n := ArithmeticFunction.vonMangoldt_nonneg

lemma Lam_zero : Lam 0 = 0 := by simp [Lam]

lemma Lam_le (n : ℕ) : Lam n ≤ n :=
  (ArithmeticFunction.vonMangoldt_le_log).trans (Real.log_le_self (Nat.cast_nonneg n))

lemma R_nonneg {N : ℕ} (hN : 1 ≤ N) : 0 ≤ R N := by
  have h : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold R
  have : 1 / (N : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]; exact h
  linarith

lemma R_lt_one {N : ℕ} (hN : 1 ≤ N) : R N < 1 := by
  have h : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold R
  have : 0 < 1 / (N : ℝ) := by positivity
  linarith

lemma summable_Lam {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable (fun n : ℕ => Lam n * r ^ n) := by
  have hnorm : ‖r‖ < 1 := by rw [Real.norm_of_nonneg h0]; exact h1
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (Lam_nonneg n) (pow_nonneg h0 n))
    (fun n => mul_le_mul_of_nonneg_right (Lam_le n) (pow_nonneg h0 n))
    (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable

lemma log_sum_bound (N : ℕ) (hN : 3 ≤ N) (P : ℕ) :
    ∑ n ∈ range P, Real.log n * (R N) ^ n ≤ N * Real.log N := by
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hNpos]
    have := Real.exp_one_lt_d9
    linarith
  have hr0 : 0 ≤ R N := R_nonneg (by omega)
  have hr1 : R N < 1 := R_lt_one (by omega)
  have h1r : 1 - R N = 1 / (N : ℝ) := by simp [R]
  generalize hr : R N = r at *
  have hnorm : ‖r‖ < 1 := by rw [Real.norm_of_nonneg hr0]; exact hr1
  have hs := ((hasSum_geometric_of_lt_one hr0 hr1).mul_left (Real.log N - 1)).add
    ((hasSum_coe_mul_geometric_of_norm_lt_one hnorm).mul_left (1 / (N : ℝ)))
  have hterm : ∀ n : ℕ, Real.log n * r ^ n ≤
      (Real.log N - 1) * r ^ n + 1 / (N : ℝ) * ((n : ℝ) * r ^ n) := by
    intro n
    have hrn := pow_nonneg hr0 n
    have hl : Real.log n ≤ Real.log N - 1 + n / N := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp; linarith
      · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        have := Real.log_le_sub_one_of_pos (div_pos hn' hNpos)
        rw [Real.log_div hn'.ne' hNpos.ne'] at this
        linarith
    calc Real.log n * r ^ n ≤ (Real.log N - 1 + n / N) * r ^ n :=
          mul_le_mul_of_nonneg_right hl hrn
      _ = _ := by ring
  have hnn : ∀ n : ℕ, 0 ≤ (Real.log N - 1) * r ^ n + 1 / (N : ℝ) * ((n : ℝ) * r ^ n) := by
    intro n
    have hrn := pow_nonneg hr0 n
    have h1 : 0 ≤ (Real.log N - 1) * r ^ n := mul_nonneg (by linarith) hrn
    have h2 : 0 ≤ 1 / (N : ℝ) * ((n : ℝ) * r ^ n) := by positivity
    linarith
  calc ∑ n ∈ range P, Real.log n * r ^ n
      ≤ ∑ n ∈ range P, ((Real.log N - 1) * r ^ n + 1 / (N : ℝ) * ((n : ℝ) * r ^ n)) :=
        sum_le_sum (fun n _ => hterm n)
    _ ≤ _ := sum_le_hasSum _ (fun i _ => hnn i) hs
    _ ≤ N * Real.log N := by
      rw [h1r]
      have e : (Real.log N - 1) * (1 / (N : ℝ))⁻¹ + 1 / (N : ℝ) * (r / (1 / (N : ℝ)) ^ 2)
          = N * Real.log N - N * (1 - r) := by
        field_simp
        ring
      rw [e]
      have : 0 ≤ (N : ℝ) * (1 - r) := mul_nonneg hNpos.le (by linarith)
      linarith

lemma double_sum (r : ℝ) (hr0 : 0 ≤ r) (T K : ℕ) :
    ∑ d ∈ Ioc 0 T, ∑ k ∈ range K, Lam d * r ^ (d * (k + 1)) ≤
      ∑ n ∈ range (T * K + 1), Real.log n * r ^ n := by
  rw [← Finset.sum_product']
  have maps : ∀ x ∈ (Ioc 0 T) ×ˢ (range K), x.1 * (x.2 + 1) ∈ range (T * K + 1) := by
    intro x hx
    simp only [mem_product, mem_Ioc, mem_range] at hx
    rw [mem_range]
    have : x.1 * (x.2 + 1) ≤ T * K := Nat.mul_le_mul hx.1.2 hx.2
    omega
  rw [← Finset.sum_fiberwise_of_maps_to maps]
  refine sum_le_sum fun n _ => ?_
  have h1 : ∑ x ∈ ((Ioc 0 T) ×ˢ (range K)).filter (fun x => x.1 * (x.2 + 1) = n),
        Lam x.1 * r ^ (x.1 * (x.2 + 1)) =
      (∑ x ∈ ((Ioc 0 T) ×ˢ (range K)).filter (fun x => x.1 * (x.2 + 1) = n), Lam x.1) * r ^ n := by
    rw [sum_mul]
    refine sum_congr rfl fun x hx => ?_
    rw [(mem_filter.mp hx).2]
  rw [h1]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hr0 n)
  have hinj : Set.InjOn (Prod.fst : ℕ × ℕ → ℕ)
      ((((Ioc 0 T) ×ˢ (range K)).filter (fun x : ℕ × ℕ => x.1 * (x.2 + 1) = n) :
        Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    have hx' := mem_filter.mp (mem_coe.mp hx)
    have hy' := mem_filter.mp (mem_coe.mp hy)
    simp only [mem_product, mem_Ioc, mem_range] at hx' hy'
    have hpos : 0 < x.1 := hx'.1.1.1
    have e : x.1 * (x.2 + 1) = x.1 * (y.2 + 1) := by
      rw [hx'.2, hxy, hy'.2]
    have e2 : x.2 + 1 = y.2 + 1 := Nat.eq_of_mul_eq_mul_left hpos e
    exact Prod.ext hxy (by omega)
  have h2 : ∑ x ∈ ((Ioc 0 T) ×ˢ (range K)).filter (fun x => x.1 * (x.2 + 1) = n), Lam x.1 =
      ∑ d ∈ (((Ioc 0 T) ×ˢ (range K)).filter (fun x => x.1 * (x.2 + 1) = n)).image Prod.fst,
        Lam d := (sum_image hinj).symm
  rw [h2]
  have h3 : Real.log n = ∑ d ∈ n.divisors, Lam d :=
    (ArithmeticFunction.vonMangoldt_sum (n := n)).symm
  rw [h3]
  refine sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => Lam_nonneg i)
  intro d hd
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hd
  have hx' := mem_filter.mp hx
  simp only [mem_product, mem_Ioc, mem_range] at hx'
  rw [Nat.mem_divisors]
  refine ⟨⟨x.2 + 1, hx'.2.symm⟩, ?_⟩
  rw [← hx'.2]
  exact Nat.mul_ne_zero (by omega) (by omega)

lemma mertens_Ioc (N : ℕ) (hN : 3 ≤ N) (T : ℕ) :
    ∑ d ∈ Ioc 0 T, Lam d * ((R N) ^ d / d) ≤ Real.log N := by
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hr0 : 0 ≤ R N := R_nonneg (by omega)
  have hr1 : R N < 1 := R_lt_one (by omega)
  have key : ∀ K : ℕ, ∑ d ∈ Ioc 0 T, Lam d * ∑ k ∈ range K, (R N) ^ (d * (k + 1)) ≤
      N * Real.log N := by
    intro K
    simp_rw [mul_sum]
    exact (double_sum _ hr0 T K).trans (log_sum_bound N hN _)
  have hhs : ∀ d ∈ Ioc 0 T, HasSum (fun k : ℕ => (R N) ^ (d * (k + 1)))
      ((R N) ^ d * (1 - (R N) ^ d)⁻¹) := by
    intro d hd
    have hd' : d ≠ 0 := by
      have := (mem_Ioc.mp hd).1
      omega
    have := (hasSum_geometric_of_lt_one (pow_nonneg hr0 d)
      (pow_lt_one₀ hr0 hr1 hd')).mul_left ((R N) ^ d)
    have e : (fun k : ℕ => (R N) ^ (d * (k + 1))) = fun i : ℕ => (R N) ^ d * ((R N) ^ d) ^ i := by
      funext k
      rw [pow_mul, pow_succ]
      ring
    rw [e]
    exact this
  have hlim : ∑ d ∈ Ioc 0 T, Lam d * ((R N) ^ d * (1 - (R N) ^ d)⁻¹) ≤ N * Real.log N :=
    le_of_tendsto' (tendsto_finsetSum _ (fun d hd =>
      ((hhs d hd).tendsto_sum_nat).const_mul (Lam d))) key
  have hcmp : ∀ d ∈ Ioc 0 T, Lam d * ((R N) ^ d / d) ≤
      1 / (N : ℝ) * (Lam d * ((R N) ^ d * (1 - (R N) ^ d)⁻¹)) := by
    intro d hd
    have hd0 : 0 < d := (mem_Ioc.mp hd).1
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd0
    have hpow : (R N) ^ d < 1 := pow_lt_one₀ hr0 hr1 hd0.ne'
    have hpos : 0 < 1 - (R N) ^ d := by linarith
    have hb : 1 + (d : ℝ) * (-(1 / (N : ℝ))) ≤ (1 + (-(1 / (N : ℝ)))) ^ d := by
      apply one_add_mul_le_pow
      have : 1 / (N : ℝ) ≤ 1 := by
        rw [div_le_one hNpos]; linarith
      linarith
    have hb' : 1 - (R N) ^ d ≤ d / N := by
      have e : 1 + (-(1 / (N : ℝ))) = R N := by simp [R]; ring
      rw [e] at hb
      have e2 : (d : ℝ) * (-(1 / (N : ℝ))) = -(d / N) := by ring
      rw [e2] at hb
      linarith
    have hinv : (N : ℝ) / d ≤ (1 - (R N) ^ d)⁻¹ := by
      rw [← inv_div]
      exact inv_anti₀ hpos hb'
    have hmain : (R N) ^ d / d ≤ 1 / (N : ℝ) * ((R N) ^ d * (1 - (R N) ^ d)⁻¹) := by
      have e : (R N) ^ d / d = 1 / (N : ℝ) * ((R N) ^ d * ((N : ℝ) / d)) := by
        field_simp
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hinv (pow_nonneg hr0 d)
    calc Lam d * ((R N) ^ d / d) ≤ Lam d *
          (1 / (N : ℝ) * ((R N) ^ d * (1 - (R N) ^ d)⁻¹)) :=
          mul_le_mul_of_nonneg_left hmain (Lam_nonneg d)
      _ = _ := by ring
  calc ∑ d ∈ Ioc 0 T, Lam d * ((R N) ^ d / d)
      ≤ ∑ d ∈ Ioc 0 T, 1 / (N : ℝ) * (Lam d * ((R N) ^ d * (1 - (R N) ^ d)⁻¹)) :=
        sum_le_sum hcmp
    _ = 1 / (N : ℝ) * ∑ d ∈ Ioc 0 T, Lam d * ((R N) ^ d * (1 - (R N) ^ d)⁻¹) := by
        rw [mul_sum]
    _ ≤ 1 / (N : ℝ) * (N * Real.log N) :=
        mul_le_mul_of_nonneg_left hlim (by positivity)
    _ = Real.log N := by field_simp

lemma sum_range_succ_eq_Ioc (f : ℕ → ℝ) (h : f 0 = 0) (T : ℕ) :
    ∑ n ∈ range (T + 1), f n = ∑ n ∈ Ioc 0 T, f n := by
  induction T with
  | zero => simp [h]
  | succ T ih =>
    rw [sum_range_succ, ih, Finset.sum_Ioc_succ_top (Nat.zero_le T)]

lemma pow_tele (x y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hxy : y ≤ x) (n : ℕ) :
    y ^ n + n * y ^ n * (x - y) ≤ x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hx0 : 0 ≤ x := hy0.trans hxy
    have hd : 0 ≤ x - y := by linarith
    have hp := pow_nonneg hy0 n
    have h1 : y ^ (n + 1) + ((n + 1 : ℕ) : ℝ) * y ^ (n + 1) * (x - y) ≤
        (y ^ n + n * y ^ n * (x - y)) * x := by
      have e : (y ^ n + n * y ^ n * (x - y)) * x -
          (y ^ (n + 1) + ((n + 1 : ℕ) : ℝ) * y ^ (n + 1) * (x - y)) =
          y ^ n * (x - y) * (1 - y) + n * y ^ n * (x - y) ^ 2 := by
        push_cast
        ring
      have h2 : 0 ≤ y ^ n * (x - y) * (1 - y) :=
        mul_nonneg (mul_nonneg hp hd) (by linarith)
      have h3 : 0 ≤ (n : ℝ) * y ^ n * (x - y) ^ 2 := by positivity
      linarith
    calc _ ≤ (y ^ n + n * y ^ n * (x - y)) * x := h1
      _ ≤ x ^ n * x := mul_le_mul_of_nonneg_right ih hx0
      _ = x ^ (n + 1) := (pow_succ x n).symm

lemma R_diff {N : ℕ} (hN : 1 ≤ N) : R (N + 1) - R N = 1 / ((N : ℝ) * ((N : ℝ) + 1)) := by
  have h : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h0 : (N : ℝ) ≠ 0 := by linarith
  have h1 : (N : ℝ) + 1 ≠ 0 := by linarith
  unfold R
  push_cast
  field_simp
  ring

lemma tele_sum (n : ℕ) (hn : 1 ≤ n) (N0 N1 : ℕ) (h : N0 ≤ N1) (hN0 : 1 ≤ N0) :
    ∑ N ∈ Ico N0 N1, (R N) ^ n / ((N : ℝ) * ((N : ℝ) + 1)) + (R N0) ^ n / n ≤ (R N1) ^ n / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  induction N1, h using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Ico_succ_top hM]
    have hM1 : 1 ≤ M := by omega
    have hdiff := R_diff hM1
    have hy0 := R_nonneg hM1
    have hy1 := (R_lt_one hM1).le
    have hxy : R M ≤ R (M + 1) := by
      have : 0 ≤ R (M + 1) - R M := by
        rw [hdiff]
        positivity
      linarith
    have ht := pow_tele (R (M + 1)) (R M) hy0 hy1 hxy n
    rw [hdiff] at ht
    have hstep : (R M) ^ n / ((M : ℝ) * ((M : ℝ) + 1)) ≤
        (R (M + 1)) ^ n / n - (R M) ^ n / n := by
      rw [← sub_div, le_div_iff₀ hn']
      have e : (R M) ^ n / ((M : ℝ) * ((M : ℝ) + 1)) * n =
          n * (R M) ^ n * (1 / ((M : ℝ) * ((M : ℝ) + 1))) := by ring
      rw [e]
      linarith
    linarith

lemma scale_finite (N0 N1 : ℕ) (hN0 : 3 ≤ N0) (h : N0 ≤ N1) (T : ℕ) :
    ∑ N ∈ Ico N0 N1, (∑ n ∈ range (T + 1), Lam n * (R N) ^ n) / ((N : ℝ) * ((N : ℝ) + 1)) ≤
      Real.log N1 := by
  simp_rw [sum_div]
  rw [sum_comm]
  calc ∑ n ∈ range (T + 1), ∑ N ∈ Ico N0 N1, Lam n * (R N) ^ n / ((N : ℝ) * ((N : ℝ) + 1))
      ≤ ∑ n ∈ range (T + 1), Lam n * ((R N1) ^ n / n) := by
        refine sum_le_sum fun n _ => ?_
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp [Lam_zero]
        · have ht := tele_sum n hn N0 N1 h (by omega)
          have hpos : 0 ≤ (R N0) ^ n / n :=
            div_nonneg (pow_nonneg (R_nonneg (by omega)) n) (Nat.cast_nonneg n)
          have : ∑ N ∈ Ico N0 N1, Lam n * (R N) ^ n / ((N : ℝ) * ((N : ℝ) + 1)) =
              Lam n * ∑ N ∈ Ico N0 N1, (R N) ^ n / ((N : ℝ) * ((N : ℝ) + 1)) := by
            rw [mul_sum]
            exact sum_congr rfl (fun _ _ => by ring)
          rw [this]
          exact mul_le_mul_of_nonneg_left (by linarith) (Lam_nonneg n)
    _ = ∑ n ∈ Ioc 0 T, Lam n * ((R N1) ^ n / n) :=
        sum_range_succ_eq_Ioc _ (by simp [Lam_zero]) T
    _ ≤ Real.log N1 := mertens_Ioc N1 (by omega) T

noncomputable def L (r : ℝ) : ℝ := ∑' n : ℕ, Lam n * r ^ n

lemma scale (N0 N1 : ℕ) (hN0 : 3 ≤ N0) (h : N0 ≤ N1) :
    ∑ N ∈ Ico N0 N1, L (R N) / ((N : ℝ) * ((N : ℝ) + 1)) ≤ Real.log N1 := by
  have ht : Filter.Tendsto (fun T : ℕ => ∑ N ∈ Ico N0 N1,
      (∑ n ∈ range (T + 1), Lam n * (R N) ^ n) / ((N : ℝ) * ((N : ℝ) + 1))) Filter.atTop
      (nhds (∑ N ∈ Ico N0 N1, L (R N) / ((N : ℝ) * ((N : ℝ) + 1)))) := by
    refine tendsto_finsetSum _ (fun N hN => ?_)
    have hN1 : 1 ≤ N := by
      have := (mem_Ico.mp hN).1
      omega
    have hs := (summable_Lam (R_nonneg hN1) (R_lt_one hN1)).hasSum.tendsto_sum_nat
    exact (((Filter.tendsto_add_atTop_iff_nat 1).2 hs)).div_const _
  exact le_of_tendsto' ht (scale_finite N0 N1 hN0 h)

lemma harm (N0 N1 : ℕ) (h : N0 ≤ N1) :
    Real.log ((N1 : ℝ) + 1) - Real.log ((N0 : ℝ) + 1) ≤ ∑ N ∈ Ico N0 N1, 1 / ((N : ℝ) + 1) := by
  induction N1, h using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Ico_succ_top hM]
    have hp : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have hq : (0 : ℝ) < (M : ℝ) + 1 + 1 := by positivity
    have := Real.log_le_sub_one_of_pos (div_pos hq hp)
    rw [Real.log_div hq.ne' hp.ne'] at this
    have e : ((M : ℝ) + 1 + 1) / ((M : ℝ) + 1) - 1 = 1 / ((M : ℝ) + 1) := by
      field_simp
      ring
    rw [e] at this
    push_cast
    linarith

lemma exists_scale (N0 : ℕ) (hN0 : 3 ≤ N0) : ∃ N, N0 ≤ N ∧ L (R N) ≤ (21 / 20) * (N : ℝ) := by
  by_contra hcon
  push Not at hcon
  have hex : ∃ N1 : ℕ, N0 ≤ N1 ∧ 0 < N1 ∧
      Real.log (N1 : ℝ) = 22 * Real.log ((N0 : ℝ) + 1) := by
    refine ⟨(N0 + 1) ^ 22, (Nat.le_succ N0).trans (Nat.le_self_pow (by norm_num) _),
      by positivity, ?_⟩
    push_cast
    rw [Real.log_pow]
    norm_num
  obtain ⟨N1, hN1, hN1pos, hlogN1⟩ := hex
  have hs := scale N0 N1 hN0 hN1
  have hh := harm N0 N1 hN1
  have hlow : ∑ N ∈ Ico N0 N1, (21 / 20 : ℝ) * (1 / ((N : ℝ) + 1)) ≤
      ∑ N ∈ Ico N0 N1, L (R N) / ((N : ℝ) * ((N : ℝ) + 1)) := by
    refine sum_le_sum fun N hN => ?_
    have hNN := (mem_Ico.mp hN).1
    have h1 := hcon N hNN
    have hNp : (0 : ℝ) < N := by
      have : 0 < N := by omega
      exact_mod_cast this
    rw [le_div_iff₀ (by positivity)]
    have e : (21 / 20 : ℝ) * (1 / ((N : ℝ) + 1)) * ((N : ℝ) * ((N : ℝ) + 1)) = 21 / 20 * N := by
      field_simp
    rw [e]
    exact h1.le
  rw [← mul_sum] at hlow
  have hb : (1 : ℝ) < (N0 : ℝ) + 1 := by
    have : (0 : ℝ) < N0 := by
      have : 0 < N0 := by omega
      exact_mod_cast this
    linarith
  have hl : 0 < Real.log ((N0 : ℝ) + 1) := Real.log_pos hb
  have hmono : Real.log (N1 : ℝ) ≤ Real.log ((N1 : ℝ) + 1) := by
    apply Real.log_le_log
    · exact_mod_cast hN1pos
    · linarith
  rw [hlogN1] at hs hmono
  linarith

lemma offdiag (m : ℕ) :
    2 * ∑ t ∈ (range (m - 1)).erase 0, Lam (m - t) * Lam (m + t) ≤
      ∑ k ∈ range (2 * m + 1), Lam k * Lam (2 * m - k) := by
  have hmem : ∀ t ∈ (range (m - 1)).erase 0, 1 ≤ t ∧ t + 1 < m := by
    intro t ht
    have h1 := mem_erase.mp ht
    have h2 := mem_range.mp h1.2
    have h3 := h1.1
    omega
  have hA : ∑ k ∈ ((range (m - 1)).erase 0).image (fun t => m - t), Lam k * Lam (2 * m - k) =
      ∑ t ∈ (range (m - 1)).erase 0, Lam (m - t) * Lam (m + t) := by
    rw [sum_image]
    · refine sum_congr rfl fun t ht => ?_
      have := hmem t ht
      have e : 2 * m - (m - t) = m + t := by omega
      rw [e]
    · intro a ha b hb hab
      have h1 := hmem a ha
      have h2 := hmem b hb
      have h3 : m - a = m - b := hab
      omega
  have hB : ∑ k ∈ ((range (m - 1)).erase 0).image (fun t => m + t), Lam k * Lam (2 * m - k) =
      ∑ t ∈ (range (m - 1)).erase 0, Lam (m - t) * Lam (m + t) := by
    rw [sum_image]
    · refine sum_congr rfl fun t ht => ?_
      have := hmem t ht
      have e : 2 * m - (m + t) = m - t := by omega
      rw [e, mul_comm]
    · intro a ha b hb hab
      have h3 : m + a = m + b := hab
      omega
  have hdisj : Disjoint (((range (m - 1)).erase 0).image (fun t => m - t))
      (((range (m - 1)).erase 0).image (fun t => m + t)) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hk1
    obtain ⟨b, hb, hab⟩ := mem_image.mp hk2
    have h1 := hmem a ha
    have h2 := hmem b hb
    omega
  have hsub : ((range (m - 1)).erase 0).image (fun t => m - t) ∪
      ((range (m - 1)).erase 0).image (fun t => m + t) ⊆ range (2 * m + 1) := by
    intro k hk
    rw [mem_range]
    rcases mem_union.mp hk with hk | hk
    · obtain ⟨a, ha, rfl⟩ := mem_image.mp hk
      omega
    · obtain ⟨a, ha, rfl⟩ := mem_image.mp hk
      have h1 := hmem a ha
      omega
  calc 2 * ∑ t ∈ (range (m - 1)).erase 0, Lam (m - t) * Lam (m + t)
      = ∑ k ∈ ((range (m - 1)).erase 0).image (fun t => m - t), Lam k * Lam (2 * m - k) +
        ∑ k ∈ ((range (m - 1)).erase 0).image (fun t => m + t), Lam k * Lam (2 * m - k) := by
        rw [hA, hB]; ring
    _ = ∑ k ∈ ((range (m - 1)).erase 0).image (fun t => m - t) ∪
        ((range (m - 1)).erase 0).image (fun t => m + t), Lam k * Lam (2 * m - k) :=
        (sum_union hdisj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub
        (fun i _ _ => mul_nonneg (Lam_nonneg _) (Lam_nonneg _))

lemma L_nonneg {r : ℝ} (h0 : 0 ≤ r) : 0 ≤ L r :=
  tsum_nonneg (fun n => mul_nonneg (Lam_nonneg n) (pow_nonneg h0 n))

lemma cauchy (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) (P : ℕ) :
    ∑ n ∈ range P, ∑ k ∈ range (n + 1), (Lam k * r ^ k) * (Lam (n - k) * r ^ (n - k)) ≤
      L r ^ 2 := by
  rw [Finset.sum_range_diag_flip P (fun a b => (Lam a * r ^ a) * (Lam b * r ^ b))]
  have hLs := summable_Lam h0 h1
  have hL0 := L_nonneg h0
  have hnn : ∀ i : ℕ, 0 ≤ Lam i * r ^ i := fun i => mul_nonneg (Lam_nonneg i) (pow_nonneg h0 i)
  have hpart : ∀ s : Finset ℕ, ∑ k ∈ s, Lam k * r ^ k ≤ L r :=
    fun s => hLs.sum_le_tsum s (fun i _ => hnn i)
  calc ∑ m ∈ range P, ∑ k ∈ range (P - m), (Lam m * r ^ m) * (Lam k * r ^ k)
      = ∑ m ∈ range P, (Lam m * r ^ m) * ∑ k ∈ range (P - m), Lam k * r ^ k := by
        simp_rw [mul_sum]
    _ ≤ ∑ m ∈ range P, (Lam m * r ^ m) * L r :=
        sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (hpart _) (hnn m)
    _ = (∑ m ∈ range P, Lam m * r ^ m) * L r := by rw [sum_mul]
    _ ≤ L r * L r := mul_le_mul_of_nonneg_right (hpart _) hL0
    _ = L r ^ 2 := by ring

lemma even_weighted (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) (X : ℕ) :
    ∑ m ∈ range X, (r ^ 2) ^ m *
        (2 * ∑ t ∈ (range (m - 1)).erase 0, Lam (m - t) * Lam (m + t)) ≤ L r ^ 2 := by
  have hc : ∀ n : ℕ, 0 ≤ ∑ k ∈ range (n + 1), (Lam k * r ^ k) * (Lam (n - k) * r ^ (n - k)) :=
    fun n => sum_nonneg fun k _ => mul_nonneg
      (mul_nonneg (Lam_nonneg _) (pow_nonneg h0 _)) (mul_nonneg (Lam_nonneg _) (pow_nonneg h0 _))
  have hstep : ∀ m : ℕ, (r ^ 2) ^ m *
      (2 * ∑ t ∈ (range (m - 1)).erase 0, Lam (m - t) * Lam (m + t)) ≤
      ∑ k ∈ range (2 * m + 1), (Lam k * r ^ k) * (Lam (2 * m - k) * r ^ (2 * m - k)) := by
    intro m
    calc _ ≤ (r ^ 2) ^ m * ∑ k ∈ range (2 * m + 1), Lam k * Lam (2 * m - k) :=
          mul_le_mul_of_nonneg_left (offdiag m) (pow_nonneg (pow_nonneg h0 2) m)
      _ = _ := by
        rw [mul_sum]
        refine sum_congr rfl fun k hk => ?_
        have hk' : k ≤ 2 * m := by
          have := mem_range.mp hk
          omega
        have e : (r ^ 2) ^ m = r ^ k * r ^ (2 * m - k) := by
          rw [← pow_mul, ← pow_add]
          congr 1
          omega
        rw [e]
        ring
  have hinj : Set.InjOn (fun m : ℕ => 2 * m) (range X : Set ℕ) := by
    intro a _ b _ hab
    have : 2 * a = 2 * b := hab
    omega
  calc _ ≤ ∑ m ∈ range X, ∑ k ∈ range (2 * m + 1),
        (Lam k * r ^ k) * (Lam (2 * m - k) * r ^ (2 * m - k)) :=
        sum_le_sum fun m _ => hstep m
    _ = ∑ n ∈ (range X).image (fun m => 2 * m), ∑ k ∈ range (n + 1),
        (Lam k * r ^ k) * (Lam (n - k) * r ^ (n - k)) := by rw [sum_image hinj]
    _ ≤ ∑ n ∈ range (2 * X), ∑ k ∈ range (n + 1),
        (Lam k * r ^ k) * (Lam (n - k) * r ^ (n - k)) := by
        refine sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hc i)
        intro n hn
        obtain ⟨a, ha, rfl⟩ := mem_image.mp hn
        have := mem_range.mp ha
        rw [mem_range]
        omega
    _ ≤ L r ^ 2 := cauchy r h0 h1 _

lemma F_lower (m : ℕ) (hm : 0 < m) :
    (1 + if 3 ∣ m then 1 else 0 : ℝ) ≤
      ∏ p ∈ (2 * m).primeFactors.filter (fun p => 2 < p), ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  have hfac : ∀ s : Finset ℕ, (∀ p ∈ s, 2 < p) →
      1 ≤ ∏ p ∈ s, ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
    intro s hs
    refine Finset.one_le_prod fun p hp => ?_
    have h2 : (3 : ℝ) ≤ p := by
      have := hs p hp
      exact_mod_cast this
    rw [le_div_iff₀ (by linarith)]
    linarith
  split_ifs with h3
  · have hmem : 3 ∈ (2 * m).primeFactors.filter (fun p => 2 < p) := by
      rw [mem_filter, Nat.mem_primeFactors]
      exact ⟨⟨Nat.prime_three, h3.trans (Nat.dvd_mul_left m 2), by omega⟩, by norm_num⟩
    have hE := Finset.mul_prod_erase _ (fun p : ℕ => ((p : ℝ) - 1) / ((p : ℝ) - 2)) hmem
    have hrest := hfac (((2 * m).primeFactors.filter (fun p => 2 < p)).erase 3)
      (fun p hp => (mem_filter.mp (mem_of_mem_erase hp)).2)
    have e3 : (((3 : ℕ) : ℝ) - 1) / (((3 : ℕ) : ℝ) - 2) = 2 := by norm_num
    simp only [e3] at hE
    rw [← hE]
    linarith
  · have := hfac ((2 * m).primeFactors.filter (fun p => 2 < p))
      (fun p hp => (mem_filter.mp hp).2)
    simpa using this

lemma numeric (e q : ℝ) (he : 0 < e) (he2 : e ≤ 1 / 1000) (hq : q = (1 - e) ^ 2) :
    33 / 100 * (1 / e) ^ 2 ≤ q / (1 - q) ^ 2 + 3 * (q ^ 3 / (1 - q ^ 3) ^ 2) := by
  have h0 : 998 / 1000 ≤ q := by rw [hq]; nlinarith
  have hq1 : q < 1 := by rw [hq]; nlinarith
  have h1 : 1 - q ≤ 2 * e := by rw [hq]; nlinarith
  have h1pos : 0 < 1 - q := by linarith
  have hq3 : (994 / 1000 : ℝ) ≤ q ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 998 / 1000) h0 3
    norm_num at this ⊢
    linarith
  have hq0 : 0 ≤ q := by linarith
  have hq31 : q ^ 3 < 1 := pow_lt_one₀ hq0 hq1 (by norm_num)
  have h2pos : 0 < 1 - q ^ 3 := by linarith
  have h2 : 1 - q ^ 3 ≤ 6 * e := by
    have e1 : 1 - q ^ 3 = (1 - q) * (1 + q + q ^ 2) := by ring
    have e2 : 1 + q + q ^ 2 ≤ 3 := by nlinarith
    rw [e1]
    have e3 : (1 - q) * (1 + q + q ^ 2) ≤ (2 * e) * 3 :=
      mul_le_mul h1 e2 (by positivity) (by positivity)
    linarith
  have hA : q / (2 * e) ^ 2 ≤ q / (1 - q) ^ 2 :=
    div_le_div_of_nonneg_left hq0 (pow_pos h1pos 2) (pow_le_pow_left₀ h1pos.le h1 2)
  have hD : q ^ 3 / (6 * e) ^ 2 ≤ q ^ 3 / (1 - q ^ 3) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (pow_pos h2pos 2) (pow_le_pow_left₀ h2pos.le h2 2)
  have hsum : 33 / 100 * (1 / e) ^ 2 ≤ q / (2 * e) ^ 2 + 3 * (q ^ 3 / (6 * e) ^ 2) := by
    have e1 : q / (2 * e) ^ 2 + 3 * (q ^ 3 / (6 * e) ^ 2) =
        (q / 4 + q ^ 3 / 12) * (1 / e) ^ 2 := by
      field_simp
      ring
    rw [e1]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    linarith
  linarith

theorem main (M0 : ℕ)
    (h : ∀ m : ℕ, M0 < m → (7 / 4 : ℝ) *
      (∏ p ∈ (2 * m).primeFactors.filter (fun p => 2 < p), ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
        (m : ℝ) ≤ ∑ t ∈ (range (m - 1)).erase 0, Lam (m - t) * Lam (m + t)) : False := by
  obtain ⟨N, hN, hL⟩ := exists_scale (1000 * (M0 + 1) + 3) (by omega)
  have hN1 : 1 ≤ N := by omega
  have hNr : (1000 : ℝ) * ((M0 : ℝ) + 1) ≤ N := by
    have : 1000 * (M0 + 1) ≤ N := by omega
    exact_mod_cast this
  have hM0 : (0 : ℝ) ≤ M0 := Nat.cast_nonneg M0
  have hNpos : (0 : ℝ) < N := by linarith
  have hr0 : 0 ≤ R N := R_nonneg hN1
  have hr1 : R N < 1 := R_lt_one hN1
  have hev := even_weighted (R N) hr0 hr1
  have hLn : 0 ≤ L (R N) := L_nonneg hr0
  have hnum := numeric (1 / (N : ℝ)) ((R N) ^ 2) (by positivity)
    (by
      rw [div_le_div_iff₀ hNpos (by norm_num)]
      linarith)
    (by simp [R])
  obtain ⟨q, hq⟩ : ∃ q, q = (R N) ^ 2 := ⟨_, rfl⟩
  rw [← hq] at hev hnum
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq1 : q < 1 := by
    rw [hq]
    exact pow_lt_one₀ hr0 hr1 (by norm_num)
  have hnorm : ‖q‖ < 1 := by rw [Real.norm_of_nonneg hq0]; exact hq1
  have hq30 : 0 ≤ q ^ 3 := pow_nonneg hq0 3
  have hnorm3 : ‖q ^ 3‖ < 1 := by
    rw [Real.norm_of_nonneg hq30]
    exact pow_lt_one₀ hq0 hq1 (by norm_num)
  have h1' := hasSum_coe_mul_geometric_of_norm_lt_one hnorm
  have h3pre := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm3).mul_left 3
  have h3 : HasSum (fun m : ℕ => if 3 ∣ m then (m : ℝ) * q ^ m else 0)
      (3 * (q ^ 3 / (1 - q ^ 3) ^ 2)) := by
    refine (Function.Injective.hasSum_iff (g := fun k : ℕ => 3 * k)
      (fun a b hab => by
        have : 3 * a = 3 * b := hab
        omega) ?_).mp ?_
    · intro x hx
      rw [if_neg]
      intro hd
      obtain ⟨c, rfl⟩ := hd
      exact hx ⟨c, rfl⟩
    · have e : ((fun m : ℕ => if 3 ∣ m then (m : ℝ) * q ^ m else 0) ∘ fun k : ℕ => 3 * k) =
          fun k : ℕ => 3 * ((k : ℝ) * (q ^ 3) ^ k) := by
        funext k
        simp [pow_mul]
        ring
      rw [e]
      exact h3pre
  have hg := h1'.add h3
  have hstep : ∀ m : ℕ, ((m : ℝ) * q ^ m + if 3 ∣ m then (m : ℝ) * q ^ m else 0) ≤
      (if m ∈ range (M0 + 1) then 2 * ((M0 : ℝ) + 1) else 0) +
        2 / 7 * (q ^ m * (2 * ∑ t ∈ (range (m - 1)).erase 0, Lam (m - t) * Lam (m + t))) := by
    intro m
    have hO : 0 ≤ ∑ t ∈ (range (m - 1)).erase 0, Lam (m - t) * Lam (m + t) :=
      sum_nonneg fun t _ => mul_nonneg (Lam_nonneg _) (Lam_nonneg _)
    have hqm : 0 ≤ q ^ m := pow_nonneg hq0 m
    have hmr : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    by_cases hm : m ≤ M0
    · have hmem : m ∈ range (M0 + 1) := mem_range.mpr (by omega)
      rw [if_pos hmem]
      have hq1m : q ^ m ≤ 1 := pow_le_one₀ hq0 hq1.le
      have hmM : (m : ℝ) ≤ M0 := by exact_mod_cast hm
      have hx : (m : ℝ) * q ^ m ≤ (M0 : ℝ) + 1 := by
        have : (m : ℝ) * q ^ m ≤ m * 1 := mul_le_mul_of_nonneg_left hq1m hmr
        linarith
      have hy : 0 ≤ (m : ℝ) * q ^ m := mul_nonneg hmr hqm
      have hz : 0 ≤ 2 / 7 * (q ^ m *
          (2 * ∑ t ∈ (range (m - 1)).erase 0, Lam (m - t) * Lam (m + t))) := by positivity
      split_ifs <;> linarith
    · have hm' : M0 < m := by omega
      have hmem : m ∉ range (M0 + 1) := by
        rw [mem_range]
        omega
      rw [if_neg hmem]
      have hF := F_lower m (by omega)
      have hh := h m hm'
      have hb : (7 / 4 : ℝ) * (1 + if 3 ∣ m then 1 else 0) * (m : ℝ) ≤
          ∑ t ∈ (range (m - 1)).erase 0, Lam (m - t) * Lam (m + t) := by
        refine le_trans ?_ hh
        refine mul_le_mul_of_nonneg_right ?_ hmr
        exact mul_le_mul_of_nonneg_left hF (by norm_num)
      have hmul := mul_le_mul_of_nonneg_right hb hqm
      split_ifs at hmul ⊢ with hd
      · nlinarith
      · nlinarith
  have hbound : ∀ X : ℕ, ∑ m ∈ range X,
      ((m : ℝ) * q ^ m + if 3 ∣ m then (m : ℝ) * q ^ m else 0) ≤
      2 * ((M0 : ℝ) + 1) ^ 2 + 2 / 7 * L (R N) ^ 2 := by
    intro X
    have hu : ∑ m ∈ range X, (if m ∈ range (M0 + 1) then 2 * ((M0 : ℝ) + 1) else 0) ≤
        2 * ((M0 : ℝ) + 1) ^ 2 := by
      rw [Finset.sum_ite_mem, sum_const, nsmul_eq_mul]
      have hcard : ((range X ∩ range (M0 + 1)).card : ℝ) ≤ (M0 : ℝ) + 1 := by
        have : (range X ∩ range (M0 + 1)).card ≤ M0 + 1 := by
          simpa using Finset.card_le_card (inter_subset_right (s₁ := range X) (s₂ := range (M0 + 1)))
        exact_mod_cast this
      have := mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ 2 * ((M0 : ℝ) + 1))
      nlinarith
    calc _ ≤ ∑ m ∈ range X, ((if m ∈ range (M0 + 1) then 2 * ((M0 : ℝ) + 1) else 0) +
          2 / 7 * (q ^ m * (2 * ∑ t ∈ (range (m - 1)).erase 0, Lam (m - t) * Lam (m + t)))) :=
          sum_le_sum fun m _ => hstep m
      _ = ∑ m ∈ range X, (if m ∈ range (M0 + 1) then 2 * ((M0 : ℝ) + 1) else 0) +
          2 / 7 * ∑ m ∈ range X,
            (q ^ m * (2 * ∑ t ∈ (range (m - 1)).erase 0, Lam (m - t) * Lam (m + t))) := by
          rw [sum_add_distrib, mul_sum]
      _ ≤ _ := add_le_add hu (mul_le_mul_of_nonneg_left (hev X) (by norm_num))
  have hlim := le_of_tendsto' hg.tendsto_sum_nat hbound
  have hL2 : L (R N) ^ 2 ≤ ((21 / 20) * (N : ℝ)) ^ 2 := pow_le_pow_left₀ hLn hL 2
  have hM2 : ((M0 : ℝ) + 1) ^ 2 ≤ ((N : ℝ) / 1000) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hN2 : 0 < (N : ℝ) ^ 2 := by positivity
  have hd : (1 / (1 / (N : ℝ))) = N := by field_simp
  rw [hd] at hnum
  nlinarith

end WGDisproof

theorem solution : ¬ (∀ (m : Nat) (hm : 2 * 10 ^ 18 < m),
    (7 / 4 : Real) *
        Finset.prod ((2 * m).primeFactors.filter (fun p => 2 < p))
          (fun p => ((p : Real) - 1) / ((p : Real) - 2)) *
        (m : Real)
      <= Finset.sum ((Finset.range (m - 1)).erase 0)
          (fun t => (ArithmeticFunction.vonMangoldt (m - t) : Real) *
            (ArithmeticFunction.vonMangoldt (m + t) : Real))) := by
  intro h
  exact WGDisproof.main (2 * 10 ^ 18) (fun m hm => h m hm)

-- Prove2me | solution 1 for PowerTwoChoices.Asymptotics.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:07:13.938952+00:00
-- url     : https://prove2.me/submissions/184f0c72-5598-479b-8755-2bcd78a854c8

import Mathlib
import Definitions.Def_PowerTwoChoices_Asymptotics_ExpectedTime

set_option autoImplicit false
open Filter Topology

namespace L3Aux

noncomputable def S (d : ℕ) (x : ℝ) : ℝ := ∑ k ∈ Finset.range d, x ^ k
noncomputable def G (d : ℕ) (x : ℝ) : ℝ := Real.log (S d x)

lemma S_ge_one (d : ℕ) (hd : 1 ≤ d) (x : ℝ) (hx : 0 ≤ x) : 1 ≤ S d x := by
  have := Finset.single_le_sum (f := fun k => x ^ k) (fun k _ => pow_nonneg hx k)
    (Finset.mem_range.2 (show 0 < d by omega) : 0 ∈ Finset.range d)
  simpa [S] using this

lemma S_le_d (d : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : S d x ≤ d := by
  unfold S
  calc ∑ k ∈ Finset.range d, x ^ k ≤ ∑ k ∈ Finset.range d, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => pow_le_one₀ hx0 hx1
    _ = d := by simp

lemma S_ge (d : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : (d : ℝ) * x ^ (d - 1) ≤ S d x := by
  unfold S
  calc (d : ℝ) * x ^ (d - 1) = ∑ k ∈ Finset.range d, x ^ (d - 1) := by simp
    _ ≤ _ := Finset.sum_le_sum fun k hk =>
      pow_le_pow_of_le_one hx0 hx1 (by have := Finset.mem_range.1 hk; omega)

lemma S_sub_one_le (d : ℕ) (hd : 1 ≤ d) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    S d x - 1 ≤ ((d : ℝ) - 1) * x := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  unfold S
  rw [Finset.sum_range_succ']
  have : ∑ k ∈ Finset.range e, x ^ (k + 1) ≤ ∑ k ∈ Finset.range e, x :=
    Finset.sum_le_sum fun k _ => by
      calc x ^ (k + 1) ≤ x ^ 1 := pow_le_pow_of_le_one hx0 hx1 (by omega)
        _ = x := pow_one x
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  push_cast
  simp
  linarith

lemma h_bound (d : ℕ) (hd : 2 ≤ d) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    |G d x - x * Real.log d| ≤ 4 * ((d : ℝ) - 1) * (x * (1 - x)) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hL : 0 < Real.log d := Real.log_pos (by linarith)
  have hLd : Real.log d ≤ (d : ℝ) - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hS1 := S_ge_one d (by omega) x hx0.le
  have hSd := S_le_d d x hx0.le hx1.le
  have hSpos : 0 < S d x := by linarith
  have hG0 : 0 ≤ G d x := Real.log_nonneg hS1
  have hGL : G d x ≤ Real.log d := Real.log_le_log hSpos hSd
  have hGu : G d x ≤ ((d : ℝ) - 1) * x := by
    have := Real.log_le_sub_one_of_pos hSpos
    have := S_sub_one_le d (by omega) x hx0.le hx1.le
    unfold G; linarith
  have hGl : Real.log d + ((d : ℝ) - 1) * (1 - x⁻¹) ≤ G d x := by
    have h1 := S_ge d x hx0.le hx1.le
    have hdpos : (0 : ℝ) < d := by linarith
    have h2 : Real.log ((d : ℝ) * x ^ (d - 1)) ≤ G d x :=
      Real.log_le_log (by positivity) h1
    rw [Real.log_mul hdpos.ne' (by positivity), Real.log_pow] at h2
    have h3 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [h3] at h2
    have h4 := Real.one_sub_inv_le_log_of_pos hx0
    nlinarith
  have hd1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by linarith
  have h1x : 0 < 1 - x := by linarith
  rw [abs_le]
  rcases le_or_gt x (1 / 2) with hx | hx
  · constructor
    · nlinarith [mul_nonneg hx0.le hd1, mul_nonneg (mul_nonneg hx0.le hd1) (show 0 ≤ 1 - 2 * x by linarith)]
    · nlinarith [mul_nonneg hx0.le hd1, mul_nonneg (mul_nonneg hx0.le hd1) (show 0 ≤ 1 - 2 * x by linarith)]
  · have hxinv : x⁻¹ < 2 := by
      rw [inv_lt_comm₀ hx0 (by norm_num)]; linarith
    have hx1' : 0 < x⁻¹ := inv_pos.2 hx0
    constructor
    · -- lower bound
      have e : (1 - x⁻¹) = -(1 - x) * x⁻¹ := by field_simp; ring
      have : ((d : ℝ) - 1) * (1 - x⁻¹) ≥ -(2 * ((d : ℝ) - 1)) * (1 - x) := by
        rw [e]
        nlinarith [mul_nonneg hd1 h1x.le, mul_nonneg (mul_nonneg hd1 h1x.le) (show 0 ≤ 2 - x⁻¹ by linarith)]
      nlinarith [mul_nonneg hd1 h1x.le, mul_nonneg (mul_nonneg hd1 h1x.le) (show 0 ≤ 2 * x - 1 by linarith)]
    · nlinarith [mul_nonneg hd1 h1x.le, mul_nonneg (mul_nonneg hd1 h1x.le) (show 0 ≤ 2 * x - 1 by linarith)]


lemma key (d : ℕ) (hd : 2 ≤ d) (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) :
    ∃ H : ℝ, |H| ≤ 4 * ((d : ℝ) - 1) ∧ Summable (fun i : ℕ => lam ^ (d ^ i)) ∧
      (∑' i : ℕ, lam ^ (d ^ i)) * Real.log d = Real.log (1 / (1 - lam)) - H := by
  set x : ℕ → ℝ := fun i => lam ^ (d ^ i) with hx
  have hx0 : ∀ i, 0 < x i := fun i => pow_pos h0 _
  have hx1 : ∀ i, x i < 1 := fun i => pow_lt_one₀ h0.le h1 (by positivity)
  have hxs : ∀ i, x (i + 1) = (x i) ^ d := by
    intro i; simp only [hx]; rw [pow_succ, pow_mul]
  have h1l : (0 : ℝ) < 1 - lam := by linarith
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  -- partial products
  have hprod : ∀ n : ℕ, ∏ i ∈ Finset.range n, S d (x i) = (1 - x n) / (1 - lam) := by
    intro n
    induction n with
    | zero => simp [hx, h1l.ne']
    | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      have hy1 : x n ≠ 1 := (hx1 n).ne
      have hfn : S d (x n) = ((x n) ^ d - 1) / (x n - 1) := by
        rw [S, ← geom_sum_eq hy1 d]
      rw [hfn, hxs]
      have : x n - 1 ≠ 0 := sub_ne_zero.2 hy1
      field_simp
      ring
  have hlog : ∀ n : ℕ, ∑ i ∈ Finset.range n, G d (x i) = Real.log ((1 - x n) / (1 - lam)) := by
    intro n
    rw [← hprod n, Real.log_prod (fun i _ => (lt_of_lt_of_le one_pos
      (S_ge_one d (by omega) (x i) (hx0 i).le)).ne')]
    rfl
  have hlim : Tendsto x atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by omega))
  have hlim2 : Tendsto (fun n : ℕ => (1 - x n) / (1 - lam)) atTop (𝓝 (1 / (1 - lam))) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hlim).div_const (1 - lam)
    simpa using this
  have hlim3 : Tendsto (fun n : ℕ => Real.log ((1 - x n) / (1 - lam))) atTop
      (𝓝 (Real.log (1 / (1 - lam)))) :=
    hlim2.log (by positivity)
  have hsumG : HasSum (fun i => G d (x i)) (Real.log (1 / (1 - lam))) := by
    show HasSum (fun i => Real.log (S d (x i))) _
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => Real.log_nonneg
      (S_ge_one d (by omega) (x i) (hx0 i).le))]
    exact hlim3.congr (fun n => (hlog n).symm)
  -- summability of x
  have hxsum : Summable x := by
    refine Summable.of_nonneg_of_le (fun i => (hx0 i).le) (fun i => ?_)
      (summable_geometric_of_lt_one h0.le h1)
    exact pow_le_pow_of_le_one h0.le h1.le (Nat.lt_pow_self (by omega)).le
  -- telescoping
  have ht : ∀ i, x i * (1 - x i) ≤ x i - x (i + 1) := by
    intro i
    rw [hxs]
    have : (x i) ^ d ≤ (x i) ^ 2 := pow_le_pow_of_le_one (hx0 i).le (hx1 i).le hd
    nlinarith
  have hpart : ∀ n, ∑ i ∈ Finset.range n, x i * (1 - x i) ≤ 1 := by
    intro n
    calc ∑ i ∈ Finset.range n, x i * (1 - x i) ≤ ∑ i ∈ Finset.range n, (x i - x (i + 1)) :=
          Finset.sum_le_sum fun i _ => ht i
      _ = x 0 - x n := Finset.sum_range_sub' x n
      _ ≤ 1 := by linarith [hx1 0, hx0 n]
  have htnn : ∀ i, 0 ≤ x i * (1 - x i) := fun i => mul_nonneg (hx0 i).le (by linarith [hx1 i])
  have htsum : Summable (fun i => x i * (1 - x i)) :=
    Summable.of_nonneg_of_le htnn (fun i => by nlinarith [hx0 i, hx1 i]) hxsum
  have htle : ∑' i, x i * (1 - x i) ≤ 1 := Real.tsum_le_of_sum_range_le htnn hpart
  -- the error terms
  set C : ℝ := 4 * ((d : ℝ) - 1) with hC
  have hCnn : 0 ≤ C := by rw [hC]; linarith
  have hbd : ∀ i, ‖G d (x i) - x i * Real.log d‖ ≤ C * (x i * (1 - x i)) := by
    intro i
    rw [Real.norm_eq_abs]
    exact h_bound d hd (x i) (hx0 i) (hx1 i)
  have hhsum : Summable (fun i => G d (x i) - x i * Real.log d) :=
    Summable.of_norm_bounded (htsum.mul_left C) hbd
  refine ⟨∑' i, (G d (x i) - x i * Real.log d), ?_, hxsum, ?_⟩
  · have := tsum_of_norm_bounded (htsum.mul_left C).hasSum hbd
    rw [tsum_mul_left] at this
    rw [← Real.norm_eq_abs]
    calc _ ≤ C * ∑' i, x i * (1 - x i) := this
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left htle hCnn
      _ = C := mul_one C
  · have e1 : ∑' i, G d (x i) = ∑' i, (G d (x i) - x i * Real.log d) + ∑' i, x i * Real.log d := by
      rw [← Summable.tsum_add hhsum (hxsum.mul_right _)]
      exact tsum_congr fun i => by ring
    rw [hsumG.tsum_eq, tsum_mul_right] at e1
    show (∑' i, x i) * Real.log d = _
    linarith

end L3Aux

open L3Aux in
theorem solution (d : ℕ) (hd : 2 ≤ d) :
    Tendsto (PowerTwoChoices.Asymptotics.Fd d) (𝓝[<] (1 : ℝ)) (𝓝 (1 / Real.log (d : ℝ))) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hL : 0 < Real.log d := Real.log_pos (by linarith)
  set Λ : ℝ → ℝ := fun lam => Real.log (1 / (1 - lam)) with hΛdef
  have hΛ : Tendsto Λ (𝓝[<] (1 : ℝ)) atTop := by
    have h1 : Tendsto (fun lam : ℝ => 1 - lam) (𝓝[<] (1 : ℝ)) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun lam : ℝ => 1 - lam) (𝓝 1) (𝓝 (1 - 1)) :=
          (tendsto_const_nhds.sub tendsto_id)
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with lam hlam
        simp only [Set.mem_Ioi]
        have : lam < 1 := hlam
        linarith
    have h2 := Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp h1)
    refine h2.congr fun lam => ?_
    simp [hΛdef, one_div]
  set C : ℝ := 4 * ((d : ℝ) - 1) with hC
  have hb : Tendsto (fun lam => C / Real.log d / Λ lam) (𝓝[<] (1 : ℝ)) (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hΛ
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with lam hlam
  obtain ⟨H, hH, -, hid⟩ := key d hd lam hlam.1 hlam.2
  have hΛpos : 0 < Λ lam := by
    simp only [hΛdef]
    apply Real.log_pos
    rw [lt_div_iff₀ (by linarith [hlam.2])]
    linarith [hlam.1]
  have hF : PowerTwoChoices.Asymptotics.Fd d lam = (∑' i : ℕ, lam ^ (d ^ i)) / Λ lam := rfl
  have e : PowerTwoChoices.Asymptotics.Fd d lam - 1 / Real.log d = -H / (Real.log d * Λ lam) := by
    rw [hF]
    have hid' : (∑' i : ℕ, lam ^ (d ^ i)) * Real.log d = Λ lam - H := hid
    field_simp
    linarith
  rw [e, norm_norm, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (mul_pos hL hΛpos)]
  calc |H| / (Real.log d * Λ lam) ≤ C / (Real.log d * Λ lam) :=
        div_le_div_of_nonneg_right hH (by positivity)
    _ = C / Real.log d / Λ lam := by rw [div_div]

-- Prove2me | solution 1 for TimeDepFolk.Asymptotic.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T22:14:49.288629+00:00
-- url     : https://prove2.me/submissions/f6e6f8c0-8786-4877-9350-6f364d00c1f3

import Mathlib
import Definitions.Def_TimeDepFolk_Asymptotic_Model

namespace TDF41

open TimeDepFolk.Asymptotic Finset

theorem pos_of_ratio (θ : Evaluation) (ε : ℝ) (hε1 : ε < 1)
    (h : ∀ t, dist (1 : ℝ) (θ.θ t / θ.θ (t + 1)) < ε) : ∀ t, 0 < θ.θ (t + 1) := by
  intro t
  rcases (θ.nonneg (t + 1)).eq_or_lt with h0 | h0
  · have := h t
    rw [← h0, div_zero, dist_zero_right, norm_one] at this
    linarith
  · exact h0

theorem step_le (θ : Evaluation) (ε : ℝ) (hε1 : ε < 1)
    (h : ∀ t, dist (1 : ℝ) (θ.θ t / θ.θ (t + 1)) < ε) (t : ℕ) :
    θ.θ t ≤ (1 + ε) * θ.θ (t + 1) := by
  have hp := pos_of_ratio θ ε hε1 h t
  have := h t
  rw [Real.dist_eq] at this
  have h2 := (abs_lt.1 this).1
  have : θ.θ t / θ.θ (t + 1) ≤ 1 + ε := by linarith
  rw [div_le_iff₀ hp] at this; linarith

theorem pow_le (θ : Evaluation) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (h : ∀ t, dist (1 : ℝ) (θ.θ t / θ.θ (t + 1)) < ε) (T : ℕ) :
    ∀ j, θ.θ T ≤ (1 + ε) ^ j * θ.θ (T + j) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have := step_le θ ε hε1 h (T + j)
    calc θ.θ T ≤ (1 + ε) ^ j * θ.θ (T + j) := ih
      _ ≤ (1 + ε) ^ j * ((1 + ε) * θ.θ (T + j + 1)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = (1 + ε) ^ (j + 1) * θ.θ (T + (j + 1)) := by rw [pow_succ, ← add_assoc]; ring

/-- Block sums are between `(m+1) θ_T / y` and `(m+1) θ_T`. -/
theorem block_bounds (θ : Evaluation) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (h : ∀ t, dist (1 : ℝ) (θ.θ t / θ.θ (t + 1)) < ε) (T m M : ℕ) (hm : m ≤ M) :
    ((m : ℝ) + 1) * θ.θ T / (1 + ε) ^ M ≤ ∑ t ∈ Icc T (T + m), θ.θ t ∧
      ∑ t ∈ Icc T (T + m), θ.θ t ≤ ((m : ℝ) + 1) * θ.θ T := by
  have hcard : ((Icc T (T + m)).card : ℝ) = m + 1 := by
    rw [Nat.card_Icc]; push_cast [show T + m + 1 - T = m + 1 by omega]; ring
  have hy : 0 < (1 + ε) ^ M := by positivity
  constructor
  · rw [div_le_iff₀ hy, ← hcard, Finset.sum_mul]
    rw [show ((Icc T (T + m)).card : ℝ) * θ.θ T = ∑ t ∈ Icc T (T + m), θ.θ T by simp]
    refine Finset.sum_le_sum fun t ht => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 ht
    obtain ⟨j, rfl⟩ : ∃ j, t = T + j := ⟨t - T, by omega⟩
    have := pow_le θ ε hε hε1 h T j
    have hj : (1 + ε) ^ j ≤ (1 + ε) ^ M := pow_le_pow_right₀ (by linarith) (by omega)
    nlinarith [θ.nonneg (T + j)]
  · rw [← hcard]
    rw [show ((Icc T (T + m)).card : ℝ) * θ.θ T = ∑ t ∈ Icc T (T + m), θ.θ T by simp]
    exact Finset.sum_le_sum fun t ht => θ.antitone (Finset.mem_Icc.1 ht).1

end TDF41

open TimeDepFolk.Asymptotic Finset

theorem solution (θ : ℕ → Evaluation) :
    IsPatient θ ↔ ∀ T1 T2 : ℕ, T1 ≤ T2 →
      TendstoUniformly
        (fun k T => (∑ t ∈ Finset.Icc T (T + T1), (θ k).θ t) /
          ∑ t ∈ Finset.Icc T (T + T2), (θ k).θ t)
        (fun _ => ((T1 : ℝ) + 1) / ((T2 : ℝ) + 1)) Filter.atTop := by
  constructor
  · intro hθ T1 T2 h12
    rw [IsPatient, Metric.tendstoUniformly_iff] at hθ
    rw [Metric.tendstoUniformly_iff]
    intro δ hδ
    -- choose `ε` with `(1+ε)^T2 < 1 + δ`
    have hcont : Filter.Tendsto (fun ε : ℝ => (1 + ε) ^ T2) (nhds 0) (nhds 1) := by
      have hc : Continuous (fun ε : ℝ => (1 + ε) ^ T2) := by fun_prop
      have := hc.tendsto (0 : ℝ)
      simpa using this
    obtain ⟨ε0, hε0, hε0'⟩ := Metric.tendsto_nhds_nhds.1 hcont δ hδ
    set ε := min (ε0 / 2) (1 / 2) with hεdef
    have hε : 0 < ε := by positivity
    have hε1 : ε < 1 := by have := min_le_right (ε0 / 2) (1 / 2); linarith
    have hεy : (1 + ε) ^ T2 < 1 + δ := by
      have h1 : dist ε 0 < ε0 := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hε]
        have := min_le_left (ε0 / 2) (1 / 2); linarith
      have := hε0' h1
      rw [Real.dist_eq] at this
      linarith [(abs_lt.1 this).2]
    filter_upwards [hθ ε hε] with k hk T
    set y := (1 + ε) ^ T2 with hydef
    have hy1 : 1 ≤ y := one_le_pow₀ (by linarith)
    have hy0 : 0 < y := by linarith
    have hθT : 0 < (θ k).θ T := by
      have := TDF41.pos_of_ratio (θ k) ε hε1 hk T
      exact lt_of_lt_of_le this ((θ k).antitone (Nat.le_succ T))
    obtain ⟨a1, a2⟩ := TDF41.block_bounds (θ k) ε hε hε1 hk T T1 T2 h12
    obtain ⟨b1, b2⟩ := TDF41.block_bounds (θ k) ε hε hε1 hk T T2 T2 le_rfl
    set N1 := ∑ t ∈ Finset.Icc T (T + T1), (θ k).θ t
    set N2 := ∑ t ∈ Finset.Icc T (T + T2), (θ k).θ t
    set c := ((T1 : ℝ) + 1) / ((T2 : ℝ) + 1) with hc
    have hT1 : (0 : ℝ) < T1 + 1 := by positivity
    have hT2 : (0 : ℝ) < T2 + 1 := by positivity
    have hc1 : c ≤ 1 := by
      rw [hc, div_le_one hT2]; exact_mod_cast Nat.succ_le_succ h12
    have hc0 : 0 < c := by positivity
    have hN2 : 0 < N2 := lt_of_lt_of_le (by positivity) b1
    -- `c / y ≤ N1 / N2 ≤ c * y`
    have hup : N1 / N2 ≤ c * y := by
      rw [div_le_iff₀ hN2, hc]
      have : (T1 + 1 : ℝ) * (θ k).θ T ≤ (T1 + 1) / (T2 + 1) * y * ((T2 + 1) * (θ k).θ T / y) := by
        field_simp; rfl
      linarith [mul_le_mul_of_nonneg_left b1 (show 0 ≤ (T1 + 1 : ℝ) / (T2 + 1) * y by positivity)]
    have hlo : c / y ≤ N1 / N2 := by
      rw [le_div_iff₀ hN2, hc]
      have : (T1 + 1 : ℝ) / (T2 + 1) / y * ((T2 + 1) * (θ k).θ T) = (T1 + 1) * (θ k).θ T / y := by
        field_simp
      nlinarith [mul_le_mul_of_nonneg_left b2 (show 0 ≤ (T1 + 1 : ℝ) / (T2 + 1) / y by positivity)]
    rw [Real.dist_eq, abs_lt]
    constructor
    · -- `N1/N2 - c < δ`
      have : c * y - c < δ := by nlinarith
      linarith
    · -- `c - N1/N2 < δ`
      have h1 : c - c / y ≤ c * y - c := by
        have : c / y ≥ c * (2 - y) := by
          rw [ge_iff_le, le_div_iff₀ hy0]; nlinarith [sq_nonneg (y - 1)]
        nlinarith
      have : c * y - c < δ := by nlinarith
      linarith
  · intro h
    have h01 := h 0 1 (Nat.zero_le 1)
    rw [Metric.tendstoUniformly_iff] at h01
    rw [IsPatient, Metric.tendstoUniformly_iff]
    intro ε hε
    set δ := min (ε / 8) (1 / 4) with hδ
    have hδ0 : 0 < δ := by positivity
    have hδ1 : δ ≤ 1 / 4 := min_le_right _ _
    have hδε : δ ≤ ε / 8 := min_le_left _ _
    filter_upwards [h01 δ hδ0] with k hk t
    have e1 : ∑ s ∈ Finset.Icc t (t + 0), (θ k).θ s = (θ k).θ t := by simp
    have e2 : ∑ s ∈ Finset.Icc t (t + 1), (θ k).θ s = (θ k).θ t + (θ k).θ (t + 1) := by
      rw [Finset.sum_Icc_succ_top (by omega), Finset.Icc_self, Finset.sum_singleton]
    have hr := hk t
    simp only [e1, e2] at hr
    norm_num at hr
    set a := (θ k).θ t
    set b := (θ k).θ (t + 1)
    have ha := (θ k).nonneg t
    have hb := (θ k).nonneg (t + 1)
    rw [Real.dist_eq, abs_lt] at hr
    -- `a + b > 0`
    have hab : 0 < a + b := by
      rcases (add_nonneg ha hb).eq_or_lt with h0 | h0
      · rw [← h0, div_zero] at hr; linarith [hr.2]
      · exact h0
    set r := a / (a + b) with hrdef
    have har : a = r * (a + b) := by rw [hrdef, div_mul_cancel₀ _ hab.ne']
    have hbpos : 0 < b := by nlinarith
    have hratio : a / b = r / (1 - r) := by
      have h1r : 0 < 1 - r := by linarith
      rw [div_eq_div_iff hbpos.ne' h1r.ne']
      nlinarith
    rw [Real.dist_eq, hratio, abs_lt]
    have h1r : 1 / 4 ≤ 1 - r := by linarith
    have h1r' : 0 < 1 - r := by linarith
    have e : 1 - r / (1 - r) = (1 - 2 * r) / (1 - r) := by field_simp; ring
    rw [e]
    constructor
    · rw [lt_div_iff₀ h1r']
      nlinarith
    · rw [div_lt_iff₀ h1r']
      nlinarith

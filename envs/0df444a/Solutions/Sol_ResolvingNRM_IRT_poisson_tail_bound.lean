-- Prove2me | solution 1 for ResolvingNRM.IRT.poisson_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T03:03:47.218883+00:00
-- url     : https://prove2.me/submissions/a9a9e7d2-58e3-436e-acec-f51a0b8328b7

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_IRT_Model

open RLPBidPrice.Unbiased Matrix ResolvingNRM.IRT Finset

/-- `e^s ≤ 1 + s + (3/4) s²` for `|s| ≤ 1`. -/
lemma irt_pt_exp_le (s : ℝ) (hs : |s| ≤ 1) : Real.exp s ≤ 1 + s + 3 / 4 * s ^ 2 := by
  have h := Real.exp_bound hs (n := 2) (by norm_num)
  have e : ∑ m ∈ range 2, s ^ m / (m.factorial : ℝ) = 1 + s := by
    simp [sum_range_succ]
  rw [e] at h
  have h2 : |s| ^ 2 = s ^ 2 := sq_abs s
  rw [h2] at h
  have h3 : ((Nat.succ 2 : ℕ) : ℝ) / ((Nat.factorial 2 : ℕ) * (2 : ℕ)) = 3 / 4 := by
    norm_num [Nat.factorial]
  rw [h3] at h
  have := (abs_le.mp h).2
  linarith

/-- Partial sums of `p_k e^{σ k}` are at most `e^{-μ} e^{μ e^σ}`. -/
lemma irt_pt_mgf_partial (μ σ : ℝ) (hμ : 0 < μ) (N : ℕ) :
    ∑ k ∈ range N, poissonPMF μ k * Real.exp (σ * k) ≤
      Real.exp (-μ) * Real.exp (μ * Real.exp σ) := by
  have hm : max μ 0 = μ := max_eq_left hμ.le
  have e : ∀ k ∈ range N, poissonPMF μ k * Real.exp (σ * k) =
      Real.exp (-μ) * ((μ * Real.exp σ) ^ k / (k.factorial : ℝ)) := by
    intro k _
    unfold poissonPMF
    rw [hm, mul_pow, ← Real.exp_nat_mul]
    have : (k : ℝ) * σ = σ * k := by ring
    rw [this]
    ring
  rw [sum_congr rfl e, ← mul_sum]
  exact mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg (by positivity) N)
    (Real.exp_pos _).le

theorem solution (μ x : ℝ) (hμ : 0 < μ) (hx : 0 < x) (hxμ : x ≤ μ) :
    ∑' k : ℕ, (if x ≤ |(k : ℝ) - μ| then poissonPMF μ k else 0) ≤
      2 * Real.exp (-(x ^ 2) / (3 * μ)) := by
  set θ : ℝ := 2 * x / (3 * μ) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one (by positivity)]; linarith
  have hpmf0 : ∀ k, 0 ≤ poissonPMF μ k := by
    intro k; unfold poissonPMF; have : 0 ≤ max μ 0 := le_max_right _ _; positivity
  -- pointwise domination
  have hpt : ∀ k : ℕ, (if x ≤ |(k : ℝ) - μ| then poissonPMF μ k else 0) ≤
      Real.exp (-θ * (μ + x)) * (poissonPMF μ k * Real.exp (θ * k)) +
        Real.exp (θ * (μ - x)) * (poissonPMF μ k * Real.exp (-θ * k)) := by
    intro k
    have hA : 0 ≤ Real.exp (-θ * (μ + x)) * (poissonPMF μ k * Real.exp (θ * k)) := by
      have := hpmf0 k; positivity
    have hB : 0 ≤ Real.exp (θ * (μ - x)) * (poissonPMF μ k * Real.exp (-θ * k)) := by
      have := hpmf0 k; positivity
    split_ifs with h
    · rcases le_abs'.mp h with h' | h'
      · -- lower tail: k ≤ μ - x
        have : 1 ≤ Real.exp (θ * (μ - x)) * Real.exp (-θ * k) := by
          rw [← Real.exp_add]
          apply Real.one_le_exp
          nlinarith
        have : poissonPMF μ k ≤ Real.exp (θ * (μ - x)) * (poissonPMF μ k * Real.exp (-θ * k)) := by
          have := hpmf0 k
          nlinarith
        linarith
      · -- upper tail: μ + x ≤ k
        have : 1 ≤ Real.exp (-θ * (μ + x)) * Real.exp (θ * k) := by
          rw [← Real.exp_add]
          apply Real.one_le_exp
          nlinarith
        have : poissonPMF μ k ≤ Real.exp (-θ * (μ + x)) * (poissonPMF μ k * Real.exp (θ * k)) := by
          have := hpmf0 k
          nlinarith
        linarith
    · linarith
  -- exponent bounds
  have hup : Real.exp (-θ * (μ + x)) * (Real.exp (-μ) * Real.exp (μ * Real.exp θ)) ≤
      Real.exp (-(x ^ 2) / (3 * μ)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he := irt_pt_exp_le θ (by rw [abs_of_nonneg hθ0]; exact hθ1)
    have h1 : μ * Real.exp θ ≤ μ * (1 + θ + 3 / 4 * θ ^ 2) := mul_le_mul_of_nonneg_left he hμ.le
    have h2 : -θ * (μ + x) + (-μ + μ * (1 + θ + 3 / 4 * θ ^ 2)) = -(x ^ 2) / (3 * μ) := by
      rw [hθ]; field_simp; ring
    linarith
  have hlo : Real.exp (θ * (μ - x)) * (Real.exp (-μ) * Real.exp (μ * Real.exp (-θ))) ≤
      Real.exp (-(x ^ 2) / (3 * μ)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he := irt_pt_exp_le (-θ) (by rw [abs_neg, abs_of_nonneg hθ0]; exact hθ1)
    have h1 : μ * Real.exp (-θ) ≤ μ * (1 + -θ + 3 / 4 * (-θ) ^ 2) :=
      mul_le_mul_of_nonneg_left he hμ.le
    have h2 : θ * (μ - x) + (-μ + μ * (1 + -θ + 3 / 4 * (-θ) ^ 2)) = -(x ^ 2) / (3 * μ) := by
      rw [hθ]; field_simp; ring
    linarith
  apply Real.tsum_le_of_sum_range_le
  · intro k; split_ifs
    · exact hpmf0 k
    · exact le_refl 0
  · intro N
    calc ∑ k ∈ range N, (if x ≤ |(k : ℝ) - μ| then poissonPMF μ k else 0)
        ≤ ∑ k ∈ range N, (Real.exp (-θ * (μ + x)) * (poissonPMF μ k * Real.exp (θ * k)) +
            Real.exp (θ * (μ - x)) * (poissonPMF μ k * Real.exp (-θ * k))) :=
          sum_le_sum fun k _ => hpt k
      _ = Real.exp (-θ * (μ + x)) * ∑ k ∈ range N, poissonPMF μ k * Real.exp (θ * k) +
            Real.exp (θ * (μ - x)) * ∑ k ∈ range N, poissonPMF μ k * Real.exp (-θ * k) := by
          rw [sum_add_distrib, mul_sum, mul_sum]
      _ ≤ Real.exp (-θ * (μ + x)) * (Real.exp (-μ) * Real.exp (μ * Real.exp θ)) +
            Real.exp (θ * (μ - x)) * (Real.exp (-μ) * Real.exp (μ * Real.exp (-θ))) := by
          gcongr
          · exact irt_pt_mgf_partial μ θ hμ N
          · exact irt_pt_mgf_partial μ (-θ) hμ N
      _ ≤ 2 * Real.exp (-(x ^ 2) / (3 * μ)) := by linarith

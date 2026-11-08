-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat22_semigroup_log_pow
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:57:34.415661+00:00
-- url     : https://prove2.me/submissions/39108170-f7ea-4a74-8aa4-b6f82ca5b28b

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped NNReal

/-- The logarithm of a continuous-at-zero nonvanishing complex semigroup is
locally additive, giving natural-time logarithmic scaling. -/
theorem solution
    (φ : ℝ≥0 → ℂ) (hφ0 : φ 0 = 1) (hφ_ne : ∀ t, φ t ≠ 0)
    (hφ_mul : ∀ s k, φ (s + k) = φ s * φ k)
    (hφ_tendsto0 : Tendsto φ (𝓝 (0 : ℝ≥0)) (𝓝 1)) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ (n : ℕ) (s : ℝ≥0), (n : ℝ≥0) * s < δ →
        log (φ ((n : ℝ≥0) * s)) = ↑(n : ℤ) * log (φ s) := by
  obtain ⟨δ, hδ_pos, hδ_re⟩ :
      ∃ δ : ℝ≥0, 0 < δ ∧ ∀ t : ℝ≥0, t < δ → 0 < (φ t).re := by
    have hmem : {z : ℂ | 0 < z.re} ∈ 𝓝 (1 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    obtain ⟨ε, hε_pos, hε_sub⟩ := Metric.eventually_nhds_iff.mp (hφ_tendsto0.eventually hmem)
    refine ⟨⟨ε, hε_pos.le⟩, ?_, fun t ht => hε_sub ?_⟩
    · exact_mod_cast hε_pos
    · simp only [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg t.coe_nonneg]
      exact_mod_cast ht
  have harg_small : ∀ t : ℝ≥0, t < δ → |arg (φ t)| < Real.pi / 2 :=
    fun t ht => abs_arg_lt_pi_div_two_iff.mpr (Or.inl (hδ_re t ht))
  have hlog_mul : ∀ s t : ℝ≥0, s < δ → t < δ →
      log (φ s * φ t) = log (φ s) + log (φ t) := by
    intro s t hs ht
    apply log_mul (hφ_ne s) (hφ_ne t)
    constructor
    · have h1 := (abs_lt.mp (harg_small s hs)).1
      have h2 := (abs_lt.mp (harg_small t ht)).1
      linarith
    · have h1 := (abs_lt.mp (harg_small s hs)).2
      have h2 := (abs_lt.mp (harg_small t ht)).2
      linarith
  have hlog_pow : ∀ (n : ℕ) (s : ℝ≥0), (n : ℝ≥0) * s < δ →
      log (φ ((n : ℝ≥0) * s)) = ↑(n : ℤ) * log (φ s) := by
    intro n
    induction n with
    | zero => intro s _; simp [show (0 : ℝ≥0) * s = 0 from zero_mul s, hφ0, log_one]
    | succ n ih =>
      intro s hs
      have hs_lt : s < δ := lt_of_le_of_lt
        (le_mul_of_one_le_left s.2 (by exact_mod_cast Nat.succ_pos n)) hs
      have hns_lt : (n : ℝ≥0) * s < δ := lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ n) s.2) hs
      rw [show ((n + 1 : ℕ) : ℝ≥0) * s = s + (n : ℝ≥0) * s from by push_cast; ring]
      rw [show φ (s + (n : ℝ≥0) * s) = φ s * φ ((n : ℝ≥0) * s) from hφ_mul _ _]
      rw [hlog_mul s ((n : ℝ≥0) * s) hs_lt hns_lt, ih s hns_lt]
      push_cast
      ring
  exact ⟨δ, hδ_pos, hlog_pow⟩

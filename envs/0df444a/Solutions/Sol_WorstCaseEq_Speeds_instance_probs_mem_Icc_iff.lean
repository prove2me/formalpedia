-- Prove2me | solution 1 for WorstCaseEq.Speeds.instance_probs_mem_Icc_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T10:38:00.571934+00:00
-- url     : https://prove2.me/submissions/49f81eb2-7c19-43ac-9eb5-2450080b0656

import Mathlib

open Real Set

theorem solution (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₁₂ : s₁ ≤ s₂) :
    (s₁ ^ 2 / (s₂ * (s₁ + s₂)) ∈ Icc (0 : ℝ) 1 ∧
        1 - s₂ ^ 2 / (s₁ * (s₁ + s₂)) ∈ Icc (0 : ℝ) 1) ↔
      s₂ ≤ goldenRatio * s₁ := by
  have hs₂ : 0 < s₂ := by linarith
  have hsum : 0 < s₁ + s₂ := by linarith
  have hdenA : 0 < s₂ * (s₁ + s₂) := by positivity
  have hdenB : 0 < s₁ * (s₁ + s₂) := by positivity
  have hA0 : 0 ≤ s₁ ^ 2 / (s₂ * (s₁ + s₂)) := by positivity
  have hA1 : s₁ ^ 2 / (s₂ * (s₁ + s₂)) ≤ 1 := by
    rw [div_le_one₀ hdenA]; nlinarith
  have hB1 : 1 - s₂ ^ 2 / (s₁ * (s₁ + s₂)) ≤ 1 := by
    have : 0 ≤ s₂ ^ 2 / (s₁ * (s₁ + s₂)) := by positivity
    linarith
  have hadd : goldenRatio + goldenConj = 1 := goldenRatio_add_goldenConj
  have hmul : goldenRatio * goldenConj = -1 := goldenRatio_mul_goldenConj
  constructor
  · rintro ⟨_, hB⟩
    have hB0 : s₂ ^ 2 ≤ s₁ * (s₁ + s₂) := by
      have := hB.1
      rwa [sub_nonneg, div_le_one₀ hdenB] at this
    have hprod : (s₂ - goldenConj * s₁) * (s₂ - goldenRatio * s₁) ≤ 0 := by
      nlinarith [hadd, hmul, hB0]
    have hpos : 0 < s₂ - goldenConj * s₁ := by
      have := goldenConj_neg
      nlinarith
    have : s₂ - goldenRatio * s₁ ≤ 0 := nonpos_of_mul_nonpos_right hprod hpos
    linarith
  · intro hφ
    refine ⟨⟨hA0, hA1⟩, ⟨?_, hB1⟩⟩
    rw [sub_nonneg, div_le_one₀ hdenB]
    nlinarith [goldenRatio_sq, hφ]

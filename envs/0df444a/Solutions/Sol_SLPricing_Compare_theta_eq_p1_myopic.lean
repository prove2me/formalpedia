-- Prove2me | solution 1 for SLPricing.Compare.theta_eq_p1_myopic
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T08:25:36.980029+00:00
-- url     : https://prove2.me/submissions/7fbe96a9-8353-4263-877e-076b87f79952

import Mathlib
import Definitions.Def_SLPricing_Compare_Model
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

open SLPricing.Compare in
theorem solution (P : Params) (hP : P.Standing) (hδ : P.δc = 0)
    (p₁ p₂ : ℝ) (hp₁ : p₁ ∈ Icc (0 : ℝ) 1) :
    IsPreEq P p₁ p₂ (Icc p₁ 1) ∧
      ∀ B : Set ℝ, IsPreEq P p₁ p₂ B → B =ᵐ[volume] Icc p₁ 1 := by
  obtain ⟨hp0, hp1⟩ := hp₁
  constructor
  · refine ⟨measurableSet_Icc, fun x hx => ⟨le_trans hp0 hx.1, hx.2⟩, ?_, ?_⟩
    · intro x hx
      unfold BuysEarlyPre
      rw [hδ, zero_mul]
      exact ⟨by linarith [hx.1], by linarith [hx.1]⟩
    · intro x hx
      unfold DelaysPre
      rw [hδ, zero_mul]
      obtain ⟨⟨_, hx1⟩, hx2⟩ := hx
      have : x < p₁ := by
        by_contra h
        push_neg at h
        exact hx2 ⟨h, hx1⟩
      linarith
  · intro B ⟨_, hBsub, hbuy, hdel⟩
    have h1 : B ⊆ Icc p₁ 1 := by
      intro x hx
      have := (hbuy x hx).1
      exact ⟨by linarith, (hBsub hx).2⟩
    have h2 : Icc p₁ 1 \ B ⊆ {p₁} := by
      intro x ⟨hx, hxB⟩
      have := hdel x ⟨⟨le_trans hp0 hx.1, hx.2⟩, hxB⟩
      unfold DelaysPre at this
      rw [hδ, zero_mul] at this
      have : x = p₁ := le_antisymm (by linarith) hx.1
      exact this
    rw [MeasureTheory.ae_eq_set]
    constructor
    · rw [Set.diff_eq_empty.mpr h1, measure_empty]
    · exact measure_mono_null h2 (Real.volume_singleton)

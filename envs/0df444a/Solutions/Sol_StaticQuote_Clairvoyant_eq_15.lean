-- Prove2me | solution 1 for StaticQuote.Clairvoyant.eq_15
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T14:59:46.894716+00:00
-- url     : https://prove2.me/submissions/3398e664-a06a-4daf-b912-9f987bf31a1c

import Mathlib
import Definitions.Def_StaticQuote_Clairvoyant_Setting
import Theorems.Thm_StaticQuote_Clairvoyant_dyadic_bound

open MeasureTheory Filter
open scoped ENNReal
open StaticQuote.Clairvoyant

theorem solution {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (Q : Model Ω)
    (hQ : Q.Standing μ) (N : ℕ) (hN : 1 ≤ N) :
    ∫⁻ ω, Q.gamma 1 N ω / (N : ℝ≥0∞) ∂μ ≤
      limsup (fun M : ℕ => ∫⁻ ω, Q.gamma 1 M ω / (M : ℝ≥0∞) ∂μ) atTop := by
  refine (dyadic_bound Q hQ N hN).2.trans ?_
  have ht : Tendsto (fun k : ℕ => 2 ^ k * N) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_) tendsto_id
    exact (Nat.lt_two_pow_self).le.trans (Nat.le_mul_of_pos_right _ hN)
  have := Filter.limsup_comp (fun M : ℕ => ∫⁻ ω, Q.gamma 1 M ω / (M : ℝ≥0∞) ∂μ)
    (fun k : ℕ => 2 ^ k * N) atTop
  rw [show (fun k : ℕ => ∫⁻ ω, Q.gamma 1 (2 ^ k * N) ω / ((2 ^ k * N : ℕ) : ℝ≥0∞) ∂μ) =
    (fun M : ℕ => ∫⁻ ω, Q.gamma 1 M ω / (M : ℝ≥0∞) ∂μ) ∘ (fun k : ℕ => 2 ^ k * N) from rfl, this]
  exact limsup_le_limsup_of_le ht

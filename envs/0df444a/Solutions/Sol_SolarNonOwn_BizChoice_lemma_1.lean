-- Prove2me | solution 1 for SolarNonOwn.BizChoice.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T10:16:33.979942+00:00
-- url     : https://prove2.me/submissions/91d46375-1c05-4ed0-9111-58785e9cfce9

import Mathlib
import Definitions.Def_SolarNonOwn_BizChoice_Model

noncomputable section
open MeasureTheory
open SolarNonOwn.BizChoice

theorem solution (prm : Params) (x : Prices) (δ : ℝ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hn : Integrable id ν) :
    ∀ i : BizOpt,
      let payoff : ℝ → ℝ := fun q => ∫ n, grossUtility q δ - monthlyCost prm x q n i ∂ν
      IsMaxOn payoff Set.univ (δ - prm.r) ∧
      (∀ q : ℝ, payoff q = payoff (δ - prm.r) → q = δ - prm.r) := by
  intro i
  -- every monthly cost is affine: a constant, plus `r * q`, plus a multiple of `n`
  obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, ∀ q n : ℝ,
      monthlyCost prm x q n i = a + prm.r * q + b * n := by
    cases i with
    | S => exact ⟨(1 - prm.alpha) * x.s, -(prm.r + prm.beta), fun q n => by
        simp only [monthlyCost]; ring⟩
    | L => exact ⟨x.l, -prm.r, fun q n => by simp only [monthlyCost]; ring⟩
    | P => exact ⟨0, x.p - prm.r, fun q n => by simp only [monthlyCost]; ring⟩
    | U => exact ⟨0, 0, fun q n => by simp only [monthlyCost]; ring⟩
  have hn' : Integrable (fun n : ℝ => n) ν := hn
  have key : ∀ q : ℝ, (∫ n, grossUtility q δ - monthlyCost prm x q n i ∂ν) =
      (δ * q - q ^ 2 / 2 - a - prm.r * q) - b * ∫ n, n ∂ν := by
    intro q
    have : (fun n => grossUtility q δ - monthlyCost prm x q n i) =
        fun n => (δ * q - q ^ 2 / 2 - a - prm.r * q) - b * n := by
      funext n; rw [hab]; simp only [grossUtility]; ring
    rw [this, integral_sub (integrable_const _) (hn'.const_mul b), integral_const,
      integral_const_mul]
    simp
  intro payoff
  have hp : ∀ q, payoff q = (δ * q - q ^ 2 / 2 - a - prm.r * q) - b * ∫ n, n ∂ν := key
  refine ⟨fun q _ => ?_, fun q hq => ?_⟩
  · show payoff q ≤ payoff (δ - prm.r)
    rw [hp, hp]
    nlinarith [sq_nonneg (q - (δ - prm.r))]
  · rw [hp, hp] at hq
    have : (q - (δ - prm.r)) ^ 2 = 0 := by nlinarith
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith

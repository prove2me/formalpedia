-- Prove2me | solution 1 for ToneAtTop.Diversion.lemma_1_convex
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T22:35:22.108478+00:00
-- url     : https://prove2.me/submissions/3406468a-4e6f-4b5e-94bb-3e3ed04dab35

import Mathlib
import Definitions.Def_ToneAtTop_Diversion_Model

namespace Prove2ToneAtTopSubmission

open _root_.ToneAtTop.Diversion

namespace ToneAtTop.Diversion.Lead34L1

open MeasureTheory

theorem tau_pos (P : Params) (hS : P.Standing) : 0 < P.tau := by
  obtain ⟨-, -, -, -, hβ, hγ, -, hη, -⟩ := hS
  exact div_pos (mul_pos (sub_pos.mpr hβ) hη) hγ

/-- The condition `τ < √(2 λ x̄ / p)` of Lemma 1 is the positivity of `λ - p τ² / (2 x̄)`. -/
theorem gap_pos (P : Params) (hS : P.Standing)
    (hL1a : P.tau < Real.sqrt (2 * P.lam * P.xbar / P.p)) :
    0 < P.lam - P.p * P.tau ^ 2 / (2 * P.xbar) := by
  have ht := tau_pos P hS
  obtain ⟨hx, -, hp, -, -, -, -, -, -⟩ := hS
  have h1 : P.tau ^ 2 < 2 * P.lam * P.xbar / P.p := (Real.lt_sqrt ht.le).mp hL1a
  have h2 : P.tau ^ 2 * P.p < 2 * P.lam * P.xbar := (lt_div_iff₀ hp).mp h1
  have h3 : P.p * P.tau ^ 2 / (2 * P.xbar) < P.lam := by
    rw [div_lt_iff₀ (by positivity)]
    linarith
  linarith

/-- On the first control region the expected loss has the closed form
`x̄ (1 - c) / 2 + (λ - p τ² / (2 x̄)) / (1 - c)`: the low type diverts on all of `(0, x̄]`, the
high type only above her tipping point `τ / (1 - c) < x̄`. -/
theorem expectedLoss_eq (P : Params) (hS : P.Standing) {c : ℝ}
    (hc : c < 1 - P.tau / P.xbar) :
    expectedLoss P c =
      P.xbar * (1 - c) / 2 + (P.lam - P.p * P.tau ^ 2 / (2 * P.xbar)) / (1 - c) := by
  have ht := tau_pos P hS
  obtain ⟨hx, -, -, -, -, hγ, -, -, -⟩ := hS
  have hu : P.tau / P.xbar < 1 - c := by linarith [hc]
  have hu0 : 0 < 1 - c := (div_pos ht hx).trans hu
  have hT0 : 0 < P.tau / (1 - c) := div_pos ht hu0
  have hT1 : P.tau / (1 - c) < P.xbar := by
    rw [div_lt_iff₀ hu0]
    have h := (div_lt_iff₀ hx).mp hu
    linarith
  -- below the tipping point only the low type diverts
  have hlow : ∀ x ∈ Set.Ioc 0 (P.tau / (1 - c)),
      (P.p * diverted P c x P.ηH + (1 - P.p) * diverted P c x 0) / P.xbar =
        (1 - P.p) * (1 - c) / P.xbar * x := by
    intro x hxI
    have hd0 : diverted P c x 0 = (1 - c) * x := by
      refine if_pos ?_
      show (0 : ℝ) < P.β * 0 + P.γ * (1 - c) * x
      rw [mul_zero, zero_add]
      exact mul_pos (mul_pos hγ hu0) hxI.1
    have hdH : diverted P c x P.ηH = 0 := by
      refine if_neg ?_
      show ¬P.ηH < P.β * P.ηH + P.γ * (1 - c) * x
      have h1 : x * (1 - c) ≤ P.tau := (le_div_iff₀ hu0).mp hxI.2
      have h2 : x * (1 - c) * P.γ ≤ (1 - P.β) * P.ηH := (le_div_iff₀ hγ).mp h1
      exact not_lt.mpr (by linarith)
    rw [hd0, hdH]
    ring
  -- above the tipping point both types divert
  have hhigh : ∀ x ∈ Set.Ioc (P.tau / (1 - c)) P.xbar,
      (P.p * diverted P c x P.ηH + (1 - P.p) * diverted P c x 0) / P.xbar =
        (1 - c) / P.xbar * x := by
    intro x hxI
    have hd0 : diverted P c x 0 = (1 - c) * x := by
      refine if_pos ?_
      show (0 : ℝ) < P.β * 0 + P.γ * (1 - c) * x
      rw [mul_zero, zero_add]
      exact mul_pos (mul_pos hγ hu0) (hT0.trans hxI.1)
    have hdH : diverted P c x P.ηH = (1 - c) * x := by
      refine if_pos ?_
      show P.ηH < P.β * P.ηH + P.γ * (1 - c) * x
      have h1 : P.tau < x * (1 - c) := (div_lt_iff₀ hu0).mp hxI.1
      have h2 : (1 - P.β) * P.ηH < x * (1 - c) * P.γ := (div_lt_iff₀ hγ).mp h1
      linarith
    rw [hd0, hdH]
    ring
  have heq1 : Set.EqOn (fun x => (1 - P.p) * (1 - c) / P.xbar * x)
      (fun x => (P.p * diverted P c x P.ηH + (1 - P.p) * diverted P c x 0) / P.xbar)
      (Set.uIoc 0 (P.tau / (1 - c))) := fun x hxI =>
    (hlow x (by rwa [Set.uIoc_of_le hT0.le] at hxI)).symm
  have heq2 : Set.EqOn (fun x => (1 - c) / P.xbar * x)
      (fun x => (P.p * diverted P c x P.ηH + (1 - P.p) * diverted P c x 0) / P.xbar)
      (Set.uIoc (P.tau / (1 - c)) P.xbar) := fun x hxI =>
    (hhigh x (by rwa [Set.uIoc_of_le hT1.le] at hxI)).symm
  have hint1 : IntervalIntegrable
      (fun x => (P.p * diverted P c x P.ηH + (1 - P.p) * diverted P c x 0) / P.xbar)
      volume 0 (P.tau / (1 - c)) :=
    (intervalIntegrable_congr heq1).mp
      ((continuous_const_mul ((1 - P.p) * (1 - c) / P.xbar)).intervalIntegrable _ _)
  have hint2 : IntervalIntegrable
      (fun x => (P.p * diverted P c x P.ηH + (1 - P.p) * diverted P c x 0) / P.xbar)
      volume (P.tau / (1 - c)) P.xbar :=
    (intervalIntegrable_congr heq2).mp
      ((continuous_const_mul ((1 - c) / P.xbar)).intervalIntegrable _ _)
  have hI1 : ∫ x in (0 : ℝ)..P.tau / (1 - c),
      (P.p * diverted P c x P.ηH + (1 - P.p) * diverted P c x 0) / P.xbar =
        ∫ x in (0 : ℝ)..P.tau / (1 - c), (1 - P.p) * (1 - c) / P.xbar * x :=
    intervalIntegral.integral_congr_ae
      (Filter.Eventually.of_forall fun _ hxI => (heq1 hxI).symm)
  have hI2 : ∫ x in P.tau / (1 - c)..P.xbar,
      (P.p * diverted P c x P.ηH + (1 - P.p) * diverted P c x 0) / P.xbar =
        ∫ x in P.tau / (1 - c)..P.xbar, (1 - c) / P.xbar * x :=
    intervalIntegral.integral_congr_ae
      (Filter.Eventually.of_forall fun _ hxI => (heq2 hxI).symm)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
  have hK : costK P.lam c = P.lam / (1 - c) := rfl
  have hE : expectedLoss P c =
      (∫ x in (0 : ℝ)..P.xbar,
        (P.p * diverted P c x P.ηH + (1 - P.p) * diverted P c x 0) / P.xbar) +
        costK P.lam c := rfl
  have hu' : 1 - c ≠ 0 := hu0.ne'
  have hx' : P.xbar ≠ 0 := hx.ne'
  rw [hE, hK, ← hsplit, hI1, hI2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_id, integral_id]
  field

/-- `c ↦ X (1 - c) / 2 + B / (1 - c)` is strictly convex on `c < 1` when `B > 0`. -/
theorem closed_strictConvexOn (X B : ℝ) (hB : 0 < B) :
    StrictConvexOn ℝ (Set.Iio 1) (fun c : ℝ => X * (1 - c) / 2 + B / (1 - c)) := by
  refine ⟨convex_Iio 1, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have hx' : (0 : ℝ) < 1 - x := sub_pos.mpr (Set.mem_Iio.mp hx)
  have hy' : (0 : ℝ) < 1 - y := sub_pos.mpr (Set.mem_Iio.mp hy)
  have hne : 1 - x ≠ 1 - y := fun h => hxy (by linarith)
  have key : (a * (1 - x) + b * (1 - y))⁻¹ < a * (1 - x)⁻¹ + b * (1 - y)⁻¹ := by
    have h := (strictConvexOn_zpow (m := -1) (by norm_num) (by norm_num)).2
      (Set.mem_Ioi.mpr hx') (Set.mem_Ioi.mpr hy') hne ha hb hab
    simp only [smul_eq_mul, zpow_neg_one] at h
    exact h
  have hinv : B / (a * (1 - x) + b * (1 - y)) < a * (B / (1 - x)) + b * (B / (1 - y)) :=
    calc B / (a * (1 - x) + b * (1 - y)) = B * (a * (1 - x) + b * (1 - y))⁻¹ :=
          div_eq_mul_inv _ _
      _ < B * (a * (1 - x)⁻¹ + b * (1 - y)⁻¹) := mul_lt_mul_of_pos_left key hB
      _ = a * (B / (1 - x)) + b * (B / (1 - y)) := by ring
  have hcomb : 1 - (a * x + b * y) = a * (1 - x) + b * (1 - y) := by linarith
  simp only [smul_eq_mul]
  rw [hcomb]
  calc X * (a * (1 - x) + b * (1 - y)) / 2 + B / (a * (1 - x) + b * (1 - y))
      < X * (a * (1 - x) + b * (1 - y)) / 2 + (a * (B / (1 - x)) + b * (B / (1 - y))) := by
        linarith
    _ = a * (X * (1 - x) / 2 + B / (1 - x)) + b * (X * (1 - y) / 2 + B / (1 - y)) := by ring

end ToneAtTop.Diversion.Lead34L1

namespace ToneAtTop.Diversion

/-- The first assertion of Lemma 1. -/
theorem lemma_1_convex (P : Params) (hS : P.Standing)
    (hL1a : P.tau < Real.sqrt (2 * P.lam * P.xbar / P.p)) :
    StrictConvexOn ℝ (Set.Ico (0 : ℝ) (1 - P.tau / P.xbar)) (expectedLoss P) := by
  have hsub : Set.Ico (0 : ℝ) (1 - P.tau / P.xbar) ⊆ Set.Iio 1 := fun c hc =>
    Set.mem_Iio.mpr (hc.2.trans (sub_lt_self 1 (div_pos (Lead34L1.tau_pos P hS) hS.1)))
  exact ((Lead34L1.closed_strictConvexOn P.xbar _ (Lead34L1.gap_pos P hS hL1a)).subset hsub
    (convex_Ico 0 (1 - P.tau / P.xbar))).congr
    fun c hc => (Lead34L1.expectedLoss_eq P hS hc.2).symm

end ToneAtTop.Diversion

end Prove2ToneAtTopSubmission

open _root_.ToneAtTop.Diversion

theorem solution (P : Params) (hS : P.Standing)
    (hL1a : P.tau < Real.sqrt (2 * P.lam * P.xbar / P.p)) :
    StrictConvexOn ℝ (Set.Ico (0 : ℝ) (1 - P.tau / P.xbar)) (expectedLoss P) := by
  exact _root_.Prove2ToneAtTopSubmission.ToneAtTop.Diversion.lemma_1_convex P hS hL1a

-- Prove2me | solution 1 for Rudin.ch10_iterated_integral
-- status  : ACCEPTED   (disprove)
-- author  : @Lucas
-- created : 2026-09-14T04:34:16.50934+00:00
-- url     : https://prove2.me/submissions/d765a43a-932a-4d4a-baee-2716c1ebc6aa

import Mathlib

open Filter Topology MeasureTheory

/-- Rudin, Theorem 10.2 as stated on the platform is refutable: without `a ≤ b` and `c ≤ d`
the continuity hypothesis can be vacuous while the oriented interval integrals still run over
a nondegenerate interval.  Counterexample: `a = 1, b = 0, c = 0, d = 1` and
`f x y = (2y - 1) / x + 1`. -/
theorem solution :
    ¬ (∀ (a b c d : ℝ) (f : ℝ → ℝ → ℝ),
        ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d) →
        (∫ x in a..b, ∫ y in c..d, f x y) = ∫ y in c..d, ∫ x in a..b, f x y) := by
  intro H
  -- the counterexample
  set f : ℝ → ℝ → ℝ := fun x y => (2 * y - 1) * x⁻¹ + 1 with hf
  -- the continuity hypothesis is vacuous, since `Set.Icc 1 0 = ∅`
  have hcont : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Set.Icc (1:ℝ) 0 ×ˢ Set.Icc (0:ℝ) 1) := by
    have hempty : Set.Icc (1:ℝ) 0 = ∅ := Set.Icc_eq_empty (by norm_num)
    rw [hempty, Set.empty_prod]
    exact continuousOn_empty _
  -- for every `x` the inner integral in `y` equals `1`
  have hinner : ∀ x : ℝ, (∫ y in (0:ℝ)..1, f x y) = 1 := by
    intro x
    have h1 : (∫ y in (0:ℝ)..1, f x y)
        = ∫ y in (0:ℝ)..1, ((2 * x⁻¹) * y + (1 - x⁻¹)) := by
      refine intervalIntegral.integral_congr ?_
      intro y _
      simp only [hf]
      ring
    have hc1 : IntervalIntegrable (fun y : ℝ => (2 * x⁻¹) * y) volume 0 1 :=
      (by fun_prop : Continuous fun y : ℝ => (2 * x⁻¹) * y).intervalIntegrable 0 1
    have hc2 : IntervalIntegrable (fun _ : ℝ => (1 - x⁻¹)) volume 0 1 :=
      _root_.intervalIntegrable_const
    rw [h1, intervalIntegral.integral_add hc1 hc2, intervalIntegral.integral_const_mul,
      integral_id, intervalIntegral.integral_const, smul_eq_mul]
    ring
  -- for every `y ≠ 1/2` the inner integral in `x` vanishes, the integrand being non-integrable
  have houter : ∀ y : ℝ, y ≠ 1 / 2 → (∫ x in (1:ℝ)..0, f x y) = 0 := by
    intro y hy
    refine intervalIntegral.integral_undef ?_
    intro h
    have hne : (2 * y - 1) ≠ 0 := fun h0 => hy (by linarith)
    have h2 : IntervalIntegrable (fun x : ℝ => (2 * y - 1) * x⁻¹) volume 1 0 := by
      simpa [hf] using h.sub (_root_.intervalIntegrable_const (c := (1:ℝ)))
    have h3 : IntervalIntegrable (fun x : ℝ => x⁻¹) volume 1 0 := by
      have h4 := h2.const_mul (2 * y - 1)⁻¹
      simp only [inv_mul_cancel_left₀ hne] at h4
      exact h4
    rw [intervalIntegrable_inv_iff] at h3
    rcases h3 with h3 | h3
    · norm_num at h3
    · exact h3 (by simp)
  have hL : (∫ x in (1:ℝ)..0, ∫ y in (0:ℝ)..1, f x y) = -1 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1:ℝ)) fun x _ => hinner x]
    simp
  have hR : (∫ y in (0:ℝ)..1, ∫ x in (1:ℝ)..0, f x y) = 0 := by
    have hae : ∀ᵐ y : ℝ, y ∈ Set.uIoc (0:ℝ) 1 → (∫ x in (1:ℝ)..0, f x y) = (0:ℝ) := by
      have h0 : ∀ᵐ y : ℝ, y ≠ 1 / 2 := by
        rw [MeasureTheory.ae_iff]
        simp
      filter_upwards [h0] with y hy _ using houter y hy
    rw [intervalIntegral.integral_congr_ae hae]
    simp
  have := H 1 0 0 1 f hcont
  rw [hL, hR] at this
  norm_num at this

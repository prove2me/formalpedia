-- Prove2me | solution 1 for YieldCheapTalk.Truthful.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:41:48.011409+00:00
-- url     : https://prove2.me/submissions/10341cbb-339c-4147-8b42-00b5e85da7b6

import Mathlib
import Definitions.Def_YieldCheapTalk_Truthful_Setting
open MeasureTheory

open YieldCheapTalk.Truthful in
theorem solution (M : Model) (hb : 0 < M.b) (hw : 0 < M.w)
    (heta : M.eta ∈ Set.Icc (0 : ℝ) 1) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsupp : ∀ᵐ x ∂ν, x ∈ Set.Icc (0 : ℝ) 1) (θ a : ℝ) (hmean : ∫ x, x ∂ν = θ)
    (hvar : ∫ x, (x - θ) ^ 2 ∂ν = M.delta ^ 2 * θ ^ 2)
    (hrange : M.eta * M.w + (1 - M.eta) * M.w * θ < a * θ) :
    0 < M.Qr θ a ∧
      (∀ Q, 0 ≤ Q → M.profitYield ν a Q ≤ M.profitYield ν a (M.Qr θ a)) ∧
      (∀ Q, 0 ≤ Q → M.profitYield ν a Q = M.profitYield ν a (M.Qr θ a) → Q = M.Qr θ a) := by
  have hθ0 : 0 ≤ θ := by
    rw [← hmean]
    exact integral_nonneg_of_ae (hsupp.mono fun x hx => hx.1)
  have hθ : 0 < θ := by
    rcases hθ0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hrange
      have : 0 ≤ M.eta * M.w := mul_nonneg heta.1 hw.le
      simp at hrange
      linarith
  have hi1 : Integrable (fun x : ℝ => x) ν := by
    refine Integrable.of_bound measurable_id.aestronglyMeasurable 1 (hsupp.mono fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]; exact hx.2
  have hi2 : Integrable (fun x : ℝ => x ^ 2) ν := by
    refine Integrable.of_bound (measurable_id.pow_const 2).aestronglyMeasurable 1
      (hsupp.mono fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]
    nlinarith [hx.1, hx.2]
  have hm2 : ∫ x, x ^ 2 ∂ν = M.delta ^ 2 * θ ^ 2 + θ ^ 2 := by
    have e : (fun x : ℝ => (x - θ) ^ 2) = fun x => x ^ 2 - 2 * θ * x + θ ^ 2 := by
      funext x; ring
    have hA : Integrable (fun x : ℝ => x ^ 2 - 2 * θ * x) ν := hi2.sub (hi1.const_mul _)
    have hB : Integrable (fun x : ℝ => 2 * θ * x) ν := hi1.const_mul _
    rw [e, integral_add hA (integrable_const _),
      integral_sub hi2 hB, integral_const_mul, hmean] at hvar
    simp at hvar
    linarith
  set K := (a - (1 - M.eta) * M.w) * θ - M.eta * M.w with hK
  have hKpos : 0 < K := by rw [hK]; nlinarith
  set D := M.b * (1 + M.delta ^ 2) * θ ^ 2 with hD
  have hDpos : 0 < D := by rw [hD]; positivity
  have hprof : ∀ Q, M.profitYield ν a Q = Q * K - D * Q ^ 2 := by
    intro Q
    unfold Model.profitYield
    have e : (fun x : ℝ => x * Q * (a - M.b * (x * Q)) - M.eta * M.w * Q
        - (1 - M.eta) * M.w * x * Q)
        = fun x => ((Q * a - (1 - M.eta) * M.w * Q) * x - (M.b * Q ^ 2) * x ^ 2)
          - M.eta * M.w * Q := by
      funext x; ring
    have hC : Integrable (fun x : ℝ => (Q * a - (1 - M.eta) * M.w * Q) * x) ν := hi1.const_mul _
    have hE : Integrable (fun x : ℝ => (M.b * Q ^ 2) * x ^ 2) ν := hi2.const_mul _
    have hF : Integrable (fun x : ℝ => (Q * a - (1 - M.eta) * M.w * Q) * x
        - (M.b * Q ^ 2) * x ^ 2) ν := hC.sub hE
    rw [e, integral_sub hF (integrable_const _),
      integral_sub hC hE, integral_const_mul, integral_const_mul,
      hmean, hm2]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [hK, hD]
    ring
  have hQr : M.Qr θ a = K / (2 * D) := by
    unfold Model.Qr; rw [hK, hD]; ring
  have hgap : ∀ Q, M.profitYield ν a (M.Qr θ a) - M.profitYield ν a Q = D * (Q - M.Qr θ a) ^ 2 := by
    intro Q
    rw [hprof, hprof, hQr]
    field_simp
    ring
  refine ⟨by rw [hQr]; positivity, fun Q _ => ?_, fun Q _ hQ => ?_⟩
  · have := hgap Q
    have : 0 ≤ D * (Q - M.Qr θ a) ^ 2 := by positivity
    linarith
  · have h := hgap Q
    rw [hQ, sub_self] at h
    have : (Q - M.Qr θ a) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h.symm with h1 | h1
      · exact absurd h1 hDpos.ne'
      · exact h1
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith

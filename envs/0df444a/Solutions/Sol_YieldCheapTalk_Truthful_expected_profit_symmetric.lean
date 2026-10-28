-- Prove2me | solution 1 for YieldCheapTalk.Truthful.expected_profit_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:13:29.917573+00:00
-- url     : https://prove2.me/submissions/31d33ff2-38be-46a5-85b9-a3af3f68cca3

import Mathlib
import Definitions.Def_YieldCheapTalk_Truthful_Setting
open MeasureTheory

open YieldCheapTalk.Truthful in
theorem solution (M : Model) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsupp : ∀ᵐ x ∂ν, x ∈ Set.Icc (0 : ℝ) 1) (θ a Q : ℝ) (hmean : ∫ x, x ∂ν = θ)
    (hvar : ∫ x, (x - θ) ^ 2 ∂ν = M.delta ^ 2 * θ ^ 2) :
    M.profitYield ν a Q =
      a * θ * Q - M.b * θ ^ 2 * (1 + M.delta ^ 2) * Q ^ 2 - M.eta * M.w * Q
        - (1 - M.eta) * M.w * θ * Q := by
  have hx : Integrable (fun x : ℝ => x) ν :=
    Integrable.of_bound measurable_id.aestronglyMeasurable 1 (by
      filter_upwards [hsupp] with x hx
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hx.1, hx.2])
  have hx2 : Integrable (fun x : ℝ => x ^ 2) ν :=
    Integrable.of_bound (measurable_id.pow_const 2).aestronglyMeasurable 1 (by
      filter_upwards [hsupp] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]; nlinarith [hx.1, hx.2])
  have hI2 : ∫ x, x ^ 2 ∂ν = θ ^ 2 * (1 + M.delta ^ 2) := by
    have e : (fun x : ℝ => (x - θ) ^ 2) = fun x => x ^ 2 - 2 * θ * x + θ ^ 2 := by
      funext x; ring
    have h1 : Integrable (fun x : ℝ => x ^ 2 - 2 * θ * x) ν := hx2.sub (hx.const_mul _)
    rw [e, integral_add h1 (integrable_const _),
      integral_sub hx2 (hx.const_mul _), integral_const_mul, integral_const, hmean] at hvar
    simp only [probReal_univ, smul_eq_mul, one_mul] at hvar
    linarith
  unfold Model.profitYield
  have e : (fun x : ℝ => x * Q * (a - M.b * (x * Q)) - M.eta * M.w * Q
      - (1 - M.eta) * M.w * x * Q) =
      fun x => ((Q * a - (1 - M.eta) * M.w * Q) * x + (-(M.b * Q ^ 2)) * x ^ 2)
        + (-(M.eta * M.w * Q)) := by
    funext x; ring
  have h1 : Integrable (fun x : ℝ => (Q * a - (1 - M.eta) * M.w * Q) * x
      + (-(M.b * Q ^ 2)) * x ^ 2) ν := (hx.const_mul _).add (hx2.const_mul _)
  rw [e, integral_add h1 (integrable_const _),
    integral_add (hx.const_mul _) (hx2.const_mul _), integral_const_mul, integral_const_mul,
    integral_const, hmean, hI2]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring

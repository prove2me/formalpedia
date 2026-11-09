-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat24_tendsto_inv_mul_re_one_sub_exp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T13:21:54.941484+00:00
-- url     : https://prove2.me/submissions/0c25afa5-b4be-4122-9dcb-7adc4d308592

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Complex Topology
open scoped Topology

private lemma leanlevyChat24_exp_first_order (z : ℂ) :
    Tendsto (fun t : ℝ => (exp ((↑t : ℂ) * z) - 1) / (↑t : ℂ))
      (𝓝[≠] (0 : ℝ)) (𝓝 z) := by
  -- The derivative of `t ↦ cexp(tz)` at `t = 0` is `z`.
  have hg : HasDerivAt (fun t : ℝ => cexp ((↑t : ℂ) * z)) z 0 := by
    -- Compose: cexp ∘ (t ↦ ↑t * z), derivative at 0 is cexp(0 * z) * z = z.
    have hf : HasDerivAt (fun t : ℝ => (↑t : ℂ) * z) (1 * z) 0 :=
      (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const z
    have hexp := hf.cexp
    simp only [ofReal_zero, zero_mul, exp_zero, one_mul, one_mul] at hexp
    exact hexp
  -- Step 3: extract the slope limit `(f(0+t) - f(0))/t → f'(0)`.
  have hslope := hg.tendsto_slope_zero
  -- Step 4: the slope is exactly `(cexp(↑t * z) - 1) / ↑t` after simplification.
  simp only [zero_add, ofReal_zero, zero_mul, exp_zero] at hslope
  exact hslope.congr (fun t => by
    show t⁻¹ • (cexp ((↑t : ℂ) * z) - 1) = (cexp ((↑t : ℂ) * z) - 1) / (↑t : ℂ)
    rw [RCLike.real_smul_eq_coe_mul (K := ℂ)]
    push_cast
    rw [inv_mul_eq_div]
    norm_cast)


theorem solution (z : ℂ) :
    Tendsto (fun t : ℝ => t⁻¹ * (1 - exp (↑t * z)).re) (𝓝[≠] 0) (𝓝 (-z).re) := by
  -- Step 1: (exp(tz)-1)/t → z, so (1-exp(tz))/t → -z
  have h2 : Tendsto (fun t : ℝ => (1 - exp ((↑t : ℂ) * z)) / (↑t : ℂ))
      (𝓝[≠] 0) (𝓝 (-z)) :=
    (leanlevyChat24_exp_first_order z).neg.congr fun t => by
      show -((exp ((↑t : ℂ) * z) - 1) / (↑t : ℂ)) = _; ring
  -- Step 2: Take Re (continuous), get Re((1-exp(tz))/t) → Re(-z)
  have h3 := (Complex.continuous_re.tendsto _).comp h2
  -- Step 3: Re(w/↑t) = t⁻¹ · Re(w) for real t
  exact h3.congr fun t => by
    simp only [Function.comp_def]
    by_cases ht : t = 0
    · simp [ht]
    · rw [div_eq_mul_inv, ← Complex.ofReal_inv, mul_comm,
        Complex.re_ofReal_mul]

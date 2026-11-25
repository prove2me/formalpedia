-- Prove2me | solution 1 for SSLWithoutPairs.exact_integral
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T10:57:58.021001+00:00
-- url     : https://prove2.me/submissions/51e2ff26-535e-4f35-9511-f7c4a40c68e9

import Mathlib
import Definitions.Def_SSLWithoutPairs_Basic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Matrix
namespace SSLWithoutPairs

theorem exact_integral (αp σ η : ℝ) (hαp : 0 < αp) (hη : 0 ≤ η) (τ p s : ℝ → ℝ)
    (hp : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt p (modeFlowP αp σ η (τ t) (p t) (s t)) (Set.Ici 0) t)
    (hs : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt s (modeFlowS σ η (τ t) (p t) (s t)) (Set.Ici 0) t) :
    ∀ t : ℝ, 0 ≤ t →
      s t = αp⁻¹ * p t ^ 2 + Real.exp (-2 * η * t) * (s 0 - αp⁻¹ * p 0 ^ 2) := by
  set h : ℝ → ℝ := fun t => Real.exp (2 * η * t) * (s t - αp⁻¹ * p t ^ 2) with hh
  have hd : ∀ t, 0 ≤ t → HasDerivWithinAt h 0 (Set.Ici 0) t := by
    intro t ht
    have he : HasDerivWithinAt (fun t => Real.exp (2 * η * t)) (Real.exp (2 * η * t) * (2 * η))
        (Set.Ici 0) t := by
      have := ((hasDerivAt_id t).const_mul (2 * η)).exp
      simpa using this.hasDerivWithinAt
    have hg := (hs t ht).sub (((hp t ht).pow 2).const_mul αp⁻¹)
    have := he.mul hg
    refine this.congr_deriv ?_
    unfold modeFlowP modeFlowS
    simp only [Pi.sub_apply, Pi.pow_apply]
    field_simp
    ring
  intro t ht
  have hc : h t = h 0 := by
    have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := h) (f' := fun _ => (0:ℝ))
      (C := 0) (a := 0) (b := t)
      (fun x hx => (hd x hx.1).mono Set.Icc_subset_Ici_self)
      (fun x _ => by simp) t ⟨ht, le_rfl⟩
    simp only [zero_mul, norm_le_zero_iff, sub_eq_zero] at key
    exact key
  simp only [hh, mul_zero, Real.exp_zero, one_mul] at hc
  have hpos : 0 < Real.exp (2 * η * t) := Real.exp_pos _
  have hinv : Real.exp (-2 * η * t) * Real.exp (2 * η * t) = 1 := by
    rw [← Real.exp_add]; simp
  have : s t - αp⁻¹ * p t ^ 2 = Real.exp (-2 * η * t) * (s 0 - αp⁻¹ * p 0 ^ 2) := by
    rw [← hc, ← mul_assoc, hinv, one_mul]
  linarith

end SSLWithoutPairs

open SSLWithoutPairs in
theorem solution (αp σ η : ℝ) (hαp : 0 < αp) (hη : 0 ≤ η) (τ p s : ℝ → ℝ)
    (hp : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt p (modeFlowP αp σ η (τ t) (p t) (s t)) (Set.Ici 0) t)
    (hs : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt s (modeFlowS σ η (τ t) (p t) (s t)) (Set.Ici 0) t) :
    ∀ t : ℝ, 0 ≤ t →
      s t = αp⁻¹ * p t ^ 2 + Real.exp (-2 * η * t) * (s 0 - αp⁻¹ * p 0 ^ 2) :=
  SSLWithoutPairs.exact_integral αp σ η hαp hη τ p s hp hs

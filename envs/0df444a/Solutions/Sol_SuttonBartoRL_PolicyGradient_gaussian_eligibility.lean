-- Prove2me | solution 1 for SuttonBartoRL.PolicyGradient.gaussian_eligibility
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T08:03:51.608078+00:00
-- url     : https://prove2.me/submissions/59f2d121-6cd9-4804-9d6f-40b67108f600

import Mathlib
import Definitions.Def_SuttonBartoRL_PolicyGradient_GaussianPolicy

set_option autoImplicit false

namespace P731f4360

lemma grad_comp_inner {d : ℕ} (v θ : EuclideanSpace ℝ (Fin d)) (g : ℝ → ℝ) (g' : ℝ)
    (hg : HasDerivAt g g' (inner ℝ θ v)) :
    HasGradientAt (fun θ' => g (inner ℝ θ' v)) (g' • v) θ := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 : HasFDerivAt (fun θ' : EuclideanSpace ℝ (Fin d) => inner ℝ θ' v)
      (innerSL ℝ v) θ := by
    have := (innerSL ℝ v).hasFDerivAt (x := θ)
    convert this using 1
    funext w
    simp [real_inner_comm]
  have h2 := hg.comp_hasFDerivAt θ h1
  have e : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))) (g' • v) = g' • innerSL ℝ v := by
    ext w
    simp
  rw [e]
  exact h2

lemma mu_part (σ a C : ℝ) (hσ : 0 < σ) (hC : 0 < C) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.log (1 / (σ * C) * Real.exp (-(a - t) ^ 2 / (2 * σ ^ 2))))
      (1 / σ ^ 2 * (a - t)) t := by
  have hpos : 0 < 1 / (σ * C) := by positivity
  have heq : (fun t : ℝ => Real.log (1 / (σ * C) * Real.exp (-(a - t) ^ 2 / (2 * σ ^ 2)))) =
      fun t => Real.log (1 / (σ * C)) + -(a - t) ^ 2 / (2 * σ ^ 2) := by
    funext t
    rw [Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp]
  rw [heq]
  have h0 : HasDerivAt (fun t : ℝ => a - t) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub a
  have h : HasDerivAt (fun t : ℝ => Real.log (1 / (σ * C)) + -(a - t) ^ 2 / (2 * σ ^ 2))
      (-((2 : ℕ) * (a - t) ^ (2 - 1) * (-1)) / (2 * σ ^ 2)) t :=
    ((h0.pow 2).neg.div_const (2 * σ ^ 2)).const_add (Real.log (1 / (σ * C)))
  refine h.congr_deriv ?_
  norm_num
  ring

lemma sigma_part (m C : ℝ) (hC : 0 < C) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.log (1 / (Real.exp t * C) *
        Real.exp (-m ^ 2 / (2 * Real.exp t ^ 2))))
      (m ^ 2 / Real.exp t ^ 2 - 1) t := by
  have heq : (fun t : ℝ => Real.log (1 / (Real.exp t * C) *
        Real.exp (-m ^ 2 / (2 * Real.exp t ^ 2)))) =
      fun t => -t - Real.log C + -m ^ 2 / 2 * Real.exp (-2 * t) := by
    funext t
    have hp : 0 < 1 / (Real.exp t * C) := by positivity
    rw [Real.log_mul hp.ne' (Real.exp_pos _).ne', Real.log_exp, one_div, Real.log_inv,
      Real.log_mul (Real.exp_pos _).ne' hC.ne', Real.log_exp]
    have : Real.exp (-2 * t) = (Real.exp t ^ 2)⁻¹ := by
      rw [← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; push_cast; ring
    rw [this]
    ring
  rw [heq]
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (-2 * t)) (Real.exp (-2 * t) * (-2)) t := by
    have := ((hasDerivAt_id t).const_mul (-2)).exp
    simpa using this
  have h : HasDerivAt (fun t : ℝ => -t - Real.log C + -m ^ 2 / 2 * Real.exp (-2 * t))
      (-1 + -m ^ 2 / 2 * (Real.exp (-2 * t) * (-2))) t :=
    (((hasDerivAt_id t).neg.sub_const (Real.log C)).add (h1.const_mul (-m ^ 2 / 2)))
  refine h.congr_deriv ?_
  have : Real.exp (-2 * t) = (Real.exp t ^ 2)⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; push_cast; ring
  rw [this]
  ring

end P731f4360

open SuttonBartoRL.PolicyGradient in
theorem solution {S : Type} {dμ dσ : ℕ}
    (xμ : S → EuclideanSpace ℝ (Fin dμ)) (xσ : S → EuclideanSpace ℝ (Fin dσ))
    (θμ : EuclideanSpace ℝ (Fin dμ)) (θσ : EuclideanSpace ℝ (Fin dσ)) (s : S) (a : ℝ) :
    HasGradientAt (fun θμ' => Real.log (gaussianPolicy xμ xσ θμ' θσ s a))
      ((1 / gaussStd xσ θσ s ^ 2 * (a - gaussMean xμ θμ s)) • xμ s) θμ ∧
    HasGradientAt (fun θσ' => Real.log (gaussianPolicy xμ xσ θμ θσ' s a))
      (((a - gaussMean xμ θμ s) ^ 2 / gaussStd xσ θσ s ^ 2 - 1) • xσ s) θσ := by
  have hC : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  constructor
  · exact P731f4360.grad_comp_inner (xμ s) θμ _ _
      (P731f4360.mu_part (gaussStd xσ θσ s) a _ (Real.exp_pos _) hC _)
  · exact P731f4360.grad_comp_inner (xσ s) θσ _ _
      (P731f4360.sigma_part (a - gaussMean xμ θμ s) _ hC _)

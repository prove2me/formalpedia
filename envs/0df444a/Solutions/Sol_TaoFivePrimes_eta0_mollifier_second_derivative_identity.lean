-- Prove2me | solution 1 for TaoFivePrimes.eta0_mollifier_second_derivative_identity
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-28T00:01:52.700877+00:00
-- url     : https://prove2.me/submissions/0161d214-e578-47c9-ac87-7c5bed3d072e

import Mathlib
import Theorems.Thm_TaoFivePrimes_eta0_lipschitz_sixteen
import Theorems.Thm_TaoFivePrimes_eta0_weak_second_derivative_identity
import Definitions.Def_TaoFivePrimes_RepresentationCount

open MeasureTheory TaoFivePrimes
open scoped Convolution
namespace Eta0Mollifier

theorem eta0_eq_zero_of_le {t : ℝ} (h : t ≤ 1/4) : eta0 t = 0 := by
  unfold eta0
  by_cases ht : 0 < t
  · rw [if_pos ht, max_eq_left, mul_zero]
    have h2 : Real.log (2*t) ≤ Real.log (1/2) := Real.log_le_log (by linarith) (by linarith)
    have h3 : Real.log (1/2 : ℝ) = -Real.log 2 := by
      rw [show (1/2 : ℝ) = (2:ℝ)⁻¹ by norm_num, Real.log_inv]
    rw [h3] at h2
    linarith [neg_le_abs (Real.log (2*t))]
  · rw [if_neg ht]

theorem eta0_eq_zero_of_ge {t : ℝ} (h : 1 ≤ t) : eta0 t = 0 := by
  unfold eta0
  have ht : 0 < t := by linarith
  rw [if_pos ht, max_eq_left, mul_zero]
  have h2 : Real.log 2 ≤ Real.log (2*t) := Real.log_le_log (by norm_num) (by linarith)
  linarith [le_abs_self (Real.log (2*t))]

private lemma eta_support : Function.support eta0 ⊆ Set.Icc (1/4:ℝ) 1 := by
  intro t ht
  constructor
  · by_contra h
    exact ht (eta0_eq_zero_of_le (le_of_not_ge h))
  · by_contra h
    exact ht (eta0_eq_zero_of_ge (le_of_not_ge h))

private lemma eta_compact : HasCompactSupport eta0 := by
  apply HasCompactSupport.intro isCompact_Icc
  intro t ht
  by_contra hn
  exact ht (eta_support hn)

private lemma eta_integrable : Integrable eta0 :=
  eta0_lipschitz_sixteen.continuous.integrable_of_hasCompactSupport eta_compact

private lemma convolution_second (φ : ℝ → ℝ)
    (hc : HasCompactSupport φ) (hs : ContDiff ℝ (⊤ : ℕ∞) φ) :
    deriv (deriv (eta0 ⋆ φ)) = eta0 ⋆ deriv (deriv φ) := by
  have he : deriv (eta0 ⋆ φ) = eta0 ⋆ deriv φ := by
    funext x
    exact (hc.hasDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      eta_integrable.locallyIntegrable (hs.of_le (by simp)) x).deriv
  rw [he]
  funext x
  exact (hc.deriv.hasDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    eta_integrable.locallyIntegrable (((contDiff_infty_iff_deriv.mp hs).2).of_le (by simp)) x).deriv

private lemma kernel_identity (φ : ℝ → ℝ)
    (hc : HasCompactSupport φ) (hs : ContDiff ℝ (⊤ : ℕ∞) φ) (x : ℝ) :
    deriv (deriv (eta0 ⋆ φ)) x =
      16 * φ (x-1/4) - 16 * φ (x-1/2) + 4 * φ (x-1) +
      (∫ t in (1/2:ℝ)..1, 4/t^2 * φ (x-t)) -
      (∫ t in (1/4:ℝ)..(1/2), 4/t^2 * φ (x-t)) := by
  rw [convolution_second φ hc hs]
  change (∫ t, eta0 t * deriv (deriv φ) (x-t)) = _
  have hz : ∀ t ∈ (Set.Icc (1/4:ℝ) 1)ᶜ,
      eta0 t * deriv (deriv φ) (x-t) = 0 := by
    intro t ht
    have h : eta0 t = 0 := by
      by_contra h
      exact ht (eta_support h)
    rw [h, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (1/4:ℝ) ≤ 1)]
  have hφ : Differentiable ℝ φ := hs.differentiable (by simp)
  have hdφ : Differentiable ℝ (deriv φ) := (contDiff_infty_iff_deriv.mp hs).2.differentiable (by simp)
  apply eta0_weak_second_derivative_identity
    (fun t => φ (x-t)) (fun t => -deriv φ (x-t))
    (fun t => deriv (deriv φ) (x-t))
  · intro t
    simpa [Function.comp_def] using (hφ (x-t)).hasDerivAt.comp t ((hasDerivAt_id t).const_sub x)
  · intro t
    convert ((hdφ (x-t)).hasDerivAt.comp t ((hasDerivAt_id t).const_sub x)).neg using 1 <;>
      first | rfl | (funext u; rfl) | simp
  · exact (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hs).2).2.continuous.comp (continuous_const.sub continuous_id)

end Eta0Mollifier

 theorem solution (φ : ℝ → ℝ)
    (hc : HasCompactSupport φ) (hs : ContDiff ℝ (⊤ : ℕ∞) φ) (x : ℝ) :
    deriv (deriv (TaoFivePrimes.eta0 ⋆ φ)) x =
      16 * φ (x-1/4) - 16 * φ (x-1/2) + 4 * φ (x-1) +
      (∫ t in (1/2:ℝ)..1, 4/t^2 * φ (x-t)) -
      (∫ t in (1/4:ℝ)..(1/2), 4/t^2 * φ (x-t)) :=
  Eta0Mollifier.kernel_identity φ hc hs x

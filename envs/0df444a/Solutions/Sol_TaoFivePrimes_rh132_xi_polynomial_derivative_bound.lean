-- Prove2me | solution 1 for TaoFivePrimes.rh132_xi_polynomial_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T01:00:32.572827+00:00
-- url     : https://prove2.me/submissions/6d2451c0-419e-406e-8bc9-0e17362ca95b

/- Cauchy derivative consequence of the height-132 disk approximation. -/
import Theorems.Thm_TaoFivePrimes_rh132_xi_approximation
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex Metric Finset

namespace Direct132Derivative

noncomputable def f (z : ℂ) : ℂ :=
  (10^43:ℂ)*RH1000Analytic.CertifiedLocalXi.xi z -
    TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14
      (10^14) 60 132 z

lemma entire : Differentiable ℂ f := by
  unfold f RH1000Analytic.CertifiedLocalXi.xi TaoFivePrimes_RHLocalRationalPolynomial
    RH1000Analytic.CertifiedLocalXi.center
  have h := differentiable_completedZeta₀
  fun_prop

lemma on_circle (z : ℂ)
    (hz : ‖z-RH1000Analytic.CertifiedLocalXi.center 132‖≤(61/20:ℝ)) :
    ∀ w ∈ sphere z (1/20:ℝ), ‖f w‖≤27/1000 := by
  intro w hw
  apply TaoFivePrimes.rh132_xi_approximation
  have h := norm_add_le (w-z) (z-RH1000Analytic.CertifiedLocalXi.center 132)
  rw [sub_add_sub_cancel,mem_sphere_iff_norm.mp hw] at h
  linarith

end Direct132Derivative

theorem solution (z : ℂ)
    (hz : ‖z-RH1000Analytic.CertifiedLocalXi.center 132‖≤(61/20:ℝ)) :
    ‖deriv (fun w : ℂ => (10^43:ℂ)*RH1000Analytic.CertifiedLocalXi.xi w -
      TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14
        (10^14) 60 132 w) z‖≤27/50 := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1
    (by norm_num : (0:ℝ)<1/20) Direct132Derivative.entire.diffContOnCl
    (Direct132Derivative.on_circle z hz)
  have hf : Direct132Derivative.f = (fun w : ℂ => (10^43:ℂ)*RH1000Analytic.CertifiedLocalXi.xi w -
      TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14
        (10^14) 60 132 w) := rfl
  rw [hf] at h
  norm_num [iteratedDeriv_one] at h ⊢
  exact h

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_deriv_deriv_log_norm_eval_1579c03559df
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:31.418552+00:00
-- url     : https://prove2.me/submissions/4a368770-8e3e-4222-a4f5-29ae9a0cc322

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm Filter Topology Polynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.FourB
theorem _root_.solution (Q : ℂ[X]) (h0 : Q.coeff 0 = 1) (h1 : Q.coeff 1 = 0) :
    deriv (deriv fun t : ℝ => Real.log ‖Q.eval (t : ℂ)‖) 0 = 2 * (Q.coeff 2).re := by
  set f : ℝ → ℂ := fun t => Q.eval (t : ℂ) with hfdef
  have hf : ∀ t : ℝ, HasDerivAt f (Q.derivative.eval (t : ℂ)) t := fun t =>
    (Q.hasDerivAt (t : ℂ)).comp_ofReal
  have hf' : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Q.derivative.eval (t : ℂ))
      (Q.derivative.derivative.eval (t : ℂ)) t := fun t =>
    (Q.derivative.hasDerivAt (t : ℂ)).comp_ofReal
  have hf0 : f 0 = 1 := by simp [f, ← Polynomial.coeff_zero_eq_eval_zero, h0]
  have hslit : ∀ᶠ t in 𝓝 (0 : ℝ), f t ∈ Complex.slitPlane := by
    have hc : Continuous f := Q.continuous.comp Complex.continuous_ofReal
    exact hc.continuousAt.eventually
      (Complex.isOpen_slitPlane.mem_nhds (by rw [hf0]; exact Complex.one_mem_slitPlane))
  have hD : (deriv fun t : ℝ => Real.log ‖f t‖) =ᶠ[𝓝 0]
      fun t => Complex.reCLM (Q.derivative.eval (t : ℂ) / f t) := by
    filter_upwards [hslit] with t ht
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t ((hf t).clog_real ht)
    have he : (fun t : ℝ => Real.log ‖f t‖) = Complex.reCLM ∘ fun t => Complex.log (f t) := by
      funext t; simp [Complex.log_re]
    rw [he]; exact h2.deriv
  rw [hD.deriv_eq]
  have hq := (hf' 0).div (hf 0) (by rw [hf0]; exact one_ne_zero)
  have h3 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hq
  rw [show (fun t : ℝ => Complex.reCLM (Q.derivative.eval (t : ℂ) / f t)) =
    Complex.reCLM ∘ ((fun t : ℝ => Q.derivative.eval (t : ℂ)) / f) from rfl, h3.deriv]
  have e1 : Q.derivative.eval ((0 : ℝ) : ℂ) = 0 := by
    rw [Complex.ofReal_zero, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
    simp [h1]
  have e2 : Q.derivative.derivative.eval ((0 : ℝ) : ℂ) = 2 * Q.coeff 2 := by
    rw [Complex.ofReal_zero, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative,
      Polynomial.coeff_derivative]
    norm_num [mul_comm]
  rw [hf0, e1, e2]
  simp
end GroundTheory.Heights₂.Heights.FourB

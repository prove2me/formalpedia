-- Prove2me | solution 1 for Sendov.eval_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:03:12.755382+00:00
-- url     : https://prove2.me/submissions/04f1cb06-e40e-4fcd-83f1-21c63deb8765

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities
import Theorems.Thm_Sendov_sumEraseProd_zero
import Theorems.Thm_Sendov_continuous_deriv_seg
attribute [local simp] Sendov.sumEraseProd_zero

set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}
open MeasureTheory
namespace Sendov
theorem _root_.solution {p : ℂ[X]} {a : ℂ} (hpa : p.eval a = 0) (w : ℂ) :
    p.eval w = (w - a) * ∫ t in (0 : ℝ)..1, (derivative p).eval (a + (t : ℂ) * (w - a)) := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => p.eval (a + (s : ℂ) * (w - a)))
      ((w - a) * (derivative p).eval (a + (t : ℂ) * (w - a))) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => a + (s : ℂ) * (w - a)) (w - a) t := by
      have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
      simpa using (h0.mul_const (w - a)).const_add a
    have h2 : HasDerivAt (fun u : ℂ => p.eval u)
        ((derivative p).eval (a + (t : ℂ) * (w - a))) (a + (t : ℂ) * (w - a)) :=
      p.hasDerivAt _
    have h3 := h2.scomp t h1
    simp only [Function.comp_def] at h3
    exact h3
  have hint : IntervalIntegrable
      (fun t : ℝ => (w - a) * (derivative p).eval (a + (t : ℂ) * (w - a))) volume 0 1 :=
    ((continuous_deriv_seg p a w).const_smul (w - a)).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hderiv t) hint
  simp only [Complex.ofReal_one, Complex.ofReal_zero, zero_mul, add_zero, one_mul] at hFTC
  rw [show a + (w - a) = w from by ring, hpa, sub_zero] at hFTC
  rw [← hFTC, intervalIntegral.integral_const_mul]
end Sendov

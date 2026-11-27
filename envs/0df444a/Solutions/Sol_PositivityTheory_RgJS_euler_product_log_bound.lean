-- Prove2me | solution 1 for PositivityTheory.RgJS.euler_product_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:21:44.858616+00:00
-- url     : https://prove2.me/submissions/2efad516-f979-4e6e-98fd-3c80df2d98f4

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_EulerLogarithms_EulerProductLogBound
import Theorems.Thm_PositivityTheory_RgJS_EulerProductLogLemmas_lterm_eq
import Theorems.Thm_PositivityTheory_RgJS_EulerProductLogLemmas_norm_zz_le
import Theorems.Thm_PositivityTheory_RgJS_EulerProductLogLemmas_x_le_half
import Theorems.Thm_PositivityTheory_RgJS_EulerProductLogLemmas_summable_maj
import Theorems.Thm_PositivityTheory_RgJS_EulerProductLogLemmas_norm_lterm_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PositivityTheory PositivityTheory.RgJS
open EulerProductLogLemmas
namespace PositivityTheory.RgJS
theorem _root_.solution : EulerLog := by
  intro W q A B _ _ α β s hP hα hβ hs
  have hq := hP.two
  have hsumn : Summable (fun p => ‖lterm q α β s p‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) (norm_lterm_le hq hα hβ)
      (summable_maj hP hs (by positivity))
  have hlt : ∀ w a b, ‖zz q α β s w a b‖ < 1 := fun w a b =>
    (norm_zz_le hq hα hβ w a b).trans_lt (by linarith [x_le_half hq hs w])
  have hfib : ∀ w, HasSum (fun k => lterm q α β s (w, k)) (∑ a, ∑ b, -Complex.log (1 - zz q α β s w a b)) := by
    intro w
    simp only [lterm_eq]
    exact hasSum_sum fun a _ => hasSum_sum fun b _ => Complex.hasSum_taylorSeries_neg_log' (hlt w a b)
  have hall : HasSum (lterm q α β s) (∑' p, lterm q α β s p) := (hsumn.of_norm).hasSum
  have hw : HasSum (fun w => ∑ a, ∑ b, -Complex.log (1 - zz q α β s w a b)) (∑' p, lterm q α β s p) :=
    hall.prod_fiberwise hfib
  have hprod := hw.cexp
  have e : ∀ w, (Complex.exp ∘ fun w => ∑ a, ∑ b, -Complex.log (1 - zz q α β s w a b)) w =
      ∏ a, ∏ b, (1 - α w a * conj (β w b) * (q w : ℂ) ^ (-s))⁻¹ := by
    intro w
    simp only [Function.comp_apply, Complex.exp_sum]
    refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
    have h0 : (1 - zz q α β s w a b) ≠ 0 := by
      intro h
      have := hlt w a b
      rw [show zz q α β s w a b = 1 by linear_combination -h, norm_one] at this
      exact lt_irrefl _ this
    rw [Complex.exp_neg, Complex.exp_log h0]
    rfl
  simp only [funext e] at hprod
  exact ⟨hsumn, hprod.tprod_eq, hprod.multipliable⟩
end PositivityTheory.RgJS

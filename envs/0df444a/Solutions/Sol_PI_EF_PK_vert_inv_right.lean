-- Prove2me | solution 1 for PI.EF.PK.vert_inv_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:06.005896+00:00
-- url     : https://prove2.me/submissions/569a9359-7ab2-4ce8-bf8f-6d864aa78ecc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real
namespace PI.EF.PK
theorem _root_.solution (c d b : ℝ) (w : ℂ) (hb : w.re < b) :
    I • ∫ y : ℝ in c..d, 1 / (((b : ℂ) + y * I) - w) =
      Complex.log (((b : ℂ) + d * I) - w) - Complex.log (((b : ℂ) + c * I) - w) := by
  have hz : ∀ y : ℝ, ((b : ℂ) + y * I - w) ∈ Complex.slitPlane := fun y => by
    rw [Complex.mem_slitPlane_iff]
    left
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    linarith
  have hne : ∀ y : ℝ, ((b : ℂ) + y * I - w) ≠ 0 := fun y => Complex.slitPlane_ne_zero (hz y)
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Complex.log ((b : ℂ) + y * I - w))
      (I * (1 / ((b : ℂ) + y * I - w))) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => (b : ℂ) + y * I - w) I y := by
      simpa using (((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (b : ℂ)).sub_const w
    have h2 := h1.clog_real (hz y)
    convert h2 using 1
    rw [one_div, div_eq_mul_inv]
  rw [smul_eq_mul, ← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)]
  exact (continuous_const.mul (continuous_const.div (by fun_prop) hne)).intervalIntegrable _ _
end PI.EF.PK

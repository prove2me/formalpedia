-- Prove2me | solution 1 for RSInt.saddle_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:08:08.620369+00:00
-- url     : https://prove2.me/submissions/d9a9f787-7721-4faa-a94d-4a919d9a78e0

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
/-  RS_B3Bound.lean -- lane RS, brick B3 (the explicit Riemann-Siegel remainder), part 3: the
    analytic estimates and THE B3 HEADLINE.  Mathlib-only (imports `RS_B3`).

    ## The headline (no `sorry`, no `native_decide`, no new axioms)

      `rs_remainder_C0` : for t >= 10000, 0 < p = rsFrac t, cos(2 pi p) ≠ 0, and every phase phi with
      |phi - rsThetaMain t| <= 1/t,
          |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) (t/2pi)^(-1/4) Psi(p)| <= 2 t^(-3/4),
      where rsRem t is the EXACT Riemann-Siegel remainder of B2 and Psi = Gabcke's C0.  With B2's
      `completed_re_eq_rs_cos` this is the classical
          Z(t) = 2 sum_{n<=N} n^(-1/2) cos(theta - t log n) + (-1)^(N-1) (t/2pi)^(-1/4) C0(p) + R,
          |R| <= 2 t^(-3/4)   (t >= 10000),
      with an explicit, kernel-checked constant (Gabcke's sharper 0.127 is NOT claimed).
      `rs_remainder_C0_alpha` is the same bound in the saddle variable a = sqrt(t/2pi):
      |...| <= (2/5) a^(-3/2).

    ## The estimates behind it

      * `integral_sq_mul_exp_neg_mul_sq` : int v^2 e^{-b v^2} dv = sqrt(pi/b) / (2b).
      * `norm_rsD_ge_two_pi_im` : |rsD z| >= 2 pi |Im z|;  `two_le_norm_rsD_midline` : |rsD| >= 2 on
        the line Re x - Im x = 1/2 (sin^2 + sinh^2 >= 1).
      * `norm_rsPhi_sub_one_le` : for |w| <= a/2 the saddle-point amplitude satisfies
            |rsPhi a w - 1| <= e e^e,   e = |w|/(2a) + |w|^2/(2a^2) + (4 pi/3)|w|^3/a
        (complex Taylor bounds for log(1+u), Mathlib `norm_log_sub_logTaylor_le`).
      * `saddle_arg_le` : along the steepest-descent line, 2 pi a^2 arg(1 + v(1+i)/a) - 2 pi (a+v) v
        <= -pi v^2 for every real v (a derivative-sign argument: the saddle is a global maximum);
        `norm_gauss_rsPhi_le` : |e^{2 pi i w^2} rsPhi a w| <= 2 e^{-pi v^2} on w = v(1+i).
      * `rsJ_eq_mid`, `norm_rsJ_le` : the tau = 2 Mordell integral moves (strip Cauchy, no pole) to the
        midline through 1/2 - p, where |rsJ p| <= 4 uniformly in p ∈ (0,1).
      * `norm_E1_integrand_near` (|v| <= a/9) / `norm_E1_integrand_far` (|v| >= a/9), `norm_rsE1_le`,
        `E1_const_le` : |rsE1 a p| <= (9/50)/a for a >= 39.

    conjecture1_proved = False.  An explicit remainder inequality for the Riemann-Siegel formula at
    finite height; nothing here bears on the Riemann Hypothesis.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

namespace RSInt

/-! ## 1. The second Gaussian moment -/





/-! ## 2. Lower bound for the denominator -/



/-! ## 3. The amplitude near the saddle point -/







/-! ## 4. The saddle point is a global maximum along the steepest-descent line -/

theorem saddle_X_mem {a : ℝ} (ha : 0 < a) (v : ℝ) : (1 : ℂ) + v * (1 + I) / a ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  rcases eq_or_ne v 0 with rfl | hv
  · left; simp
  · right; simp [Complex.div_im, hv, ha.ne']







/-! ## 4b. Integrability of the second Gaussian moment -/



/-! ## 5. The tau = 2 Mordell integral is uniformly bounded -/











/-! ## 6. The error integral `rsE1` is `O(1/a)` -/

















/-! ## 7. The explicit C0 remainder bound -/













end RSInt

end

/-  RS_B3Bound.lean -- lane RS, brick B3 (the explicit Riemann-Siegel remainder), part 3: the
    analytic estimates and THE B3 HEADLINE.  Mathlib-only (imports `RS_B3`).

    ## The headline (no `sorry`, no `native_decide`, no new axioms)

      `rs_remainder_C0` : for t >= 10000, 0 < p = rsFrac t, cos(2 pi p) ≠ 0, and every phase phi with
      |phi - rsThetaMain t| <= 1/t,
          |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) (t/2pi)^(-1/4) Psi(p)| <= 2 t^(-3/4),
      where rsRem t is the EXACT Riemann-Siegel remainder of B2 and Psi = Gabcke's C0.  With B2's
      `completed_re_eq_rs_cos` this is the classical
          Z(t) = 2 sum_{n<=N} n^(-1/2) cos(theta - t log n) + (-1)^(N-1) (t/2pi)^(-1/4) C0(p) + R,
          |R| <= 2 t^(-3/4)   (t >= 10000),
      with an explicit, kernel-checked constant (Gabcke's sharper 0.127 is NOT claimed).
      `rs_remainder_C0_alpha` is the same bound in the saddle variable a = sqrt(t/2pi):
      |...| <= (2/5) a^(-3/2).

    ## The estimates behind it

      * `integral_sq_mul_exp_neg_mul_sq` : int v^2 e^{-b v^2} dv = sqrt(pi/b) / (2b).
      * `norm_rsD_ge_two_pi_im` : |rsD z| >= 2 pi |Im z|;  `two_le_norm_rsD_midline` : |rsD| >= 2 on
        the line Re x - Im x = 1/2 (sin^2 + sinh^2 >= 1).
      * `norm_rsPhi_sub_one_le` : for |w| <= a/2 the saddle-point amplitude satisfies
            |rsPhi a w - 1| <= e e^e,   e = |w|/(2a) + |w|^2/(2a^2) + (4 pi/3)|w|^3/a
        (complex Taylor bounds for log(1+u), Mathlib `norm_log_sub_logTaylor_le`).
      * `saddle_arg_le` : along the steepest-descent line, 2 pi a^2 arg(1 + v(1+i)/a) - 2 pi (a+v) v
        <= -pi v^2 for every real v (a derivative-sign argument: the saddle is a global maximum);
        `norm_gauss_rsPhi_le` : |e^{2 pi i w^2} rsPhi a w| <= 2 e^{-pi v^2} on w = v(1+i).
      * `rsJ_eq_mid`, `norm_rsJ_le` : the tau = 2 Mordell integral moves (strip Cauchy, no pole) to the
        midline through 1/2 - p, where |rsJ p| <= 4 uniformly in p ∈ (0,1).
      * `norm_E1_integrand_near` (|v| <= a/9) / `norm_E1_integrand_far` (|v| >= a/9), `norm_rsE1_le`,
        `E1_const_le` : |rsE1 a p| <= (9/50)/a for a >= 39.

    conjecture1_proved = False.  An explicit remainder inequality for the Riemann-Siegel formula at
    finite height; nothing here bears on the Riemann Hypothesis.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

section
namespace RSInt
end RSInt
open RSInt

/-! ## 1. The second Gaussian moment -/





/-! ## 2. Lower bound for the denominator -/



/-! ## 3. The amplitude near the saddle point -/







/-! ## 4. The saddle point is a global maximum along the steepest-descent line -/



theorem solution {a : ℝ} (ha : 0 < a) (v : ℝ) :
    HasDerivAt (fun v : ℝ => 2 * π * a ^ 2 * (Complex.log (1 + v * (1 + I) / a)).im -
      2 * π * (a + v) * v + π * v ^ 2)
      (-(2 * π * v * (3 * a ^ 2 + 4 * a * v + 2 * v ^ 2) / ((a + v) ^ 2 + v ^ 2))) v := by
  have hX : HasDerivAt (fun v : ℝ => (1 : ℂ) + v * (1 + I) / a) ((1 + I) / a) v := by
    have := ((hasDerivAt_id (v : ℂ)).mul_const ((1 + I) / (a : ℂ))).const_add (1 : ℂ)
    have h2 := this.comp_ofReal (z := v)
    convert h2 using 1
    · ext y; simp; ring
    · simp
  have hlog := (Complex.hasDerivAt_log (saddle_X_mem ha v)).comp v hX
  have him := (Complex.imCLM.hasFDerivAt).comp_hasDerivAt v hlog
  have hpoly : HasDerivAt (fun v : ℝ => -(2 * π * (a + v) * v) + π * v ^ 2)
      (-(2 * π * (a + 2 * v)) + 2 * π * v) v := by
    have h1 : HasDerivAt (fun v : ℝ => 2 * π * (a + v) * v) (2 * π * (a + 2 * v)) v := by
      have := (((hasDerivAt_id' v).const_add a).const_mul (2 * π)).mul (hasDerivAt_id' v)
      convert this using 1 <;> first | rfl | ring
    have h2 : HasDerivAt (fun v : ℝ => π * v ^ 2) (2 * π * v) v := by
      have := (hasDerivAt_pow 2 v).const_mul π
      convert this using 1 <;> first | rfl | (norm_num <;> ring)
    exact h1.neg.add h2
  have htot := (him.const_mul (2 * π * a ^ 2)).add hpoly
  refine htot.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · -- the derivative value
    have hden : (a + v) ^ 2 + v ^ 2 ≠ 0 := by
      have : 0 < (a + v) ^ 2 + v ^ 2 := by
        rcases eq_or_ne v 0 with rfl | hv
        · simp; positivity
        · have := sq_pos_of_ne_zero hv; positivity
      exact this.ne'
    simp only [Complex.imCLM_apply]
    have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
    have hXv : (1 : ℂ) + v * (1 + I) / a = ((a + v) + v * I) / a := by
      field_simp; ring
    rw [hXv]
    have hz : ((a : ℂ) + v) + v * I ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
      have h2 := congrArg Complex.im h; simp at h2
      rw [h2] at this; linarith
    rw [show (((a : ℂ) + v + v * I) / a)⁻¹ * ((1 + I) / a) = (1 + I) / ((a : ℂ) + v + v * I) by
      field_simp]
    rw [Complex.div_im]
    simp [Complex.normSq_apply]
    field_simp
    ring
  · exact Eventually.of_forall fun y => by simp; ring

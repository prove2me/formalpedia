-- Prove2me | solution 1 for RSInt.two_le_norm_rsD_midline
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:10:08.762636+00:00
-- url     : https://prove2.me/submissions/a5923e91-c038-465a-b40b-7e0206aa3535

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









/-! ## 4b. Integrability of the second Gaussian moment -/



/-! ## 5. The tau = 2 Mordell integral is uniformly bounded -/

theorem rsD_midline_re_im (v : ℝ) :
    (rsD ((1 / 2 : ℂ) + v * (1 + I))).re =
        (Real.exp (π * v) - Real.exp (-(π * v))) * Real.sin (π * v) ∧
      (rsD ((1 / 2 : ℂ) + v * (1 + I))).im =
        (Real.exp (π * v) + Real.exp (-(π * v))) * Real.cos (π * v) := by
  unfold rsD
  have h1 : (↑π * I * ((1 / 2 : ℂ) + v * (1 + I))) =
      ((-(π * v) : ℝ) : ℂ) + ((π * v + π / 2 : ℝ) : ℂ) * I := by
    push_cast
    linear_combination (↑π * (v : ℂ)) * I_sq
  have h2 : -(↑π * I * ((1 / 2 : ℂ) + v * (1 + I))) =
      ((π * v : ℝ) : ℂ) + ((-(π * v + π / 2) : ℝ) : ℂ) * I := by
    rw [h1]; push_cast; ring
  rw [h2, h1]
  simp only [Complex.sub_re, Complex.sub_im, Complex.exp_re, Complex.exp_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, add_zero, zero_add]
  rw [Real.cos_neg, Real.sin_neg, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  constructor <;> ring









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









/-! ## 4b. Integrability of the second Gaussian moment -/



/-! ## 5. The tau = 2 Mordell integral is uniformly bounded -/




theorem solution (v : ℝ) : 2 ≤ ‖rsD ((1 / 2 : ℂ) + v * (1 + I))‖ := by
  obtain ⟨hre, him⟩ := rsD_midline_re_im v
  set z := rsD ((1 / 2 : ℂ) + v * (1 + I))
  set E := Real.exp (π * v)
  set F := Real.exp (-(π * v))
  set s := Real.sin (π * v)
  set c := Real.cos (π * v)
  have hEF : E * F = 1 := by rw [← Real.exp_add]; simp
  have hsinh : (π * v) ^ 2 ≤ Real.sinh (π * v) ^ 2 :=
    sq_le_sq.mpr (by rw [Real.abs_sinh]; exact Real.self_le_sinh_iff.mpr (abs_nonneg _))
  have hsin : s ^ 2 ≤ (π * v) ^ 2 := Real.sin_sq_le_sq
  have hsh : Real.sinh (π * v) = (E - F) / 2 := Real.sinh_eq _
  have hsc : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have key : 4 * s ^ 2 ≤ (E - F) ^ 2 := by
    rw [hsh, show ((E - F) / 2) ^ 2 = (E - F) ^ 2 / 4 by ring] at hsinh
    linarith
  have hsq : 4 ≤ ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
    have e1 : (E - F) * s * ((E - F) * s) + (E + F) * c * ((E + F) * c) =
        (E - F) ^ 2 * (s ^ 2 + c ^ 2) + 4 * (E * F) * c ^ 2 := by ring
    rw [e1, hsc, hEF]
    nlinarith
  nlinarith [norm_nonneg z]

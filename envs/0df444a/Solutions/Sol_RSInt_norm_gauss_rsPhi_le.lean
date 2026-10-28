-- Prove2me | solution 1 for RSInt.norm_gauss_rsPhi_le
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:11:54.621654+00:00
-- url     : https://prove2.me/submissions/d77283b5-bc92-4fc4-b710-82bf85dbb7c4

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_saddle_arg_le
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
    ‖cexp (2 * ↑π * I * ((v : ℂ) * (1 + I)) ^ 2) * rsPhi a ((v : ℂ) * (1 + I))‖ ≤
      2 * Real.exp (-(π * v ^ 2)) := by
  set w : ℂ := (v : ℂ) * (1 + I) with hw
  set X : ℂ := 1 + w / a with hX
  have hXs : X ∈ slitPlane := by
    have := saddle_X_mem ha v
    rw [hX, hw]; simpa [mul_div_assoc] using this
  have hX0 : X ≠ 0 := slitPlane_ne_zero hXs
  have hXnorm : 1 / 4 ≤ ‖X‖ := by
    have h1 := Complex.abs_re_le_norm X
    have h2 := Complex.abs_im_le_norm X
    have hre : X.re = 1 + v / a := by rw [hX, hw]; simp [Complex.div_re]; field_simp
    have him : X.im = v / a := by rw [hX, hw]; simp [Complex.div_im]; field_simp
    rw [hre] at h1; rw [him] at h2
    rcases le_total (v / a) (-(1 / 2)) with h | h
    · have : 1 / 2 ≤ |v / a| := by rw [abs_of_neg (by linarith)]; linarith
      linarith
    · have : 1 / 2 ≤ |1 + v / a| := by rw [abs_of_nonneg (by linarith)]; linarith
      linarith
  unfold rsPhi
  rw [← hX, ← mul_assoc, ← Complex.exp_add, norm_mul, Complex.norm_exp,
    Complex.norm_cpow_of_ne_zero hX0]
  have hre : (2 * (π : ℂ) * I * w ^ 2 + (2 * (π : ℂ) * I * a * w - (π : ℂ) * I * w ^ 2)).re =
      -(2 * π * (a + v) * v) := by
    rw [hw]; simp [pow_two, mul_re, mul_im]; ring
  have hsre : (-((1 / 2 : ℂ) + 2 * (π : ℂ) * a ^ 2 * I)).re = -(1 / 2) := by simp [pow_two]
  have hsim : (-((1 / 2 : ℂ) + 2 * (π : ℂ) * a ^ 2 * I)).im = -(2 * π * a ^ 2) := by
    simp [pow_two]
  rw [hre, hsre, hsim]
  have hargb := saddle_arg_le ha v
  have hXeq : (1 : ℂ) + (v : ℂ) * (1 + I) / a = X := by rw [hX, hw]
  rw [hXeq] at hargb
  have hpow : ‖X‖ ^ (-(1 / 2 : ℝ)) ≤ 2 := by
    calc ‖X‖ ^ (-(1 / 2 : ℝ)) ≤ (1 / 4 : ℝ) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hXnorm (by norm_num)
      _ = 2 := by
          rw [Real.rpow_neg (by norm_num), show (1 / 4 : ℝ) = (1 / 2) ^ (2 : ℝ) by norm_num,
            ← Real.rpow_mul (by norm_num)]
          norm_num
  have hexp : Real.exp (-(2 * π * (a + v) * v)) / Real.exp (X.arg * -(2 * π * a ^ 2)) =
      Real.exp (2 * π * a ^ 2 * X.arg - 2 * π * (a + v) * v) := by
    rw [← Real.exp_sub]; congr 1; ring
  calc Real.exp (-(2 * π * (a + v) * v)) * (‖X‖ ^ (-(1 / 2 : ℝ)) /
        Real.exp (X.arg * -(2 * π * a ^ 2)))
      = ‖X‖ ^ (-(1 / 2 : ℝ)) * (Real.exp (-(2 * π * (a + v) * v)) /
          Real.exp (X.arg * -(2 * π * a ^ 2))) := by ring
    _ = ‖X‖ ^ (-(1 / 2 : ℝ)) * Real.exp (2 * π * a ^ 2 * X.arg - 2 * π * (a + v) * v) := by
          rw [hexp]
    _ ≤ 2 * Real.exp (-(π * v ^ 2)) :=
          mul_le_mul hpow (Real.exp_le_exp.mpr hargb) (Real.exp_pos _).le (by norm_num)

-- Prove2me | solution 1 for RSInt.saddle_arg_le
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:09:52.308706+00:00
-- url     : https://prove2.me/submissions/e396109d-de73-4dbd-bacf-7a257afc6157

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_saddle_hasDerivAt

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
    2 * π * a ^ 2 * Complex.arg (1 + v * (1 + I) / a) - 2 * π * (a + v) * v ≤ -(π * v ^ 2) := by
  set h : ℝ → ℝ := fun v => 2 * π * a ^ 2 * (Complex.log (1 + v * (1 + I) / a)).im -
    2 * π * (a + v) * v + π * v ^ 2 with hh
  have hderiv := saddle_hasDerivAt ha
  have hcont : Continuous h := continuous_iff_continuousAt.mpr fun v => (hderiv v).continuousAt
  have hdiff : Differentiable ℝ h := fun v => (hderiv v).differentiableAt
  have h0 : h 0 = 0 := by simp [hh]
  have hpos : ∀ v, 0 < 3 * a ^ 2 + 4 * a * v + 2 * v ^ 2 := by
    intro v; nlinarith [sq_nonneg (v + a), sq_nonneg a, ha]
  have hden : ∀ v : ℝ, 0 < (a + v) ^ 2 + v ^ 2 := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simp; positivity
    · have := sq_pos_of_ne_zero hv; positivity
  have hle : h v ≤ 0 := by
    rcases le_total 0 v with hv | hv
    · have hanti : AntitoneOn h (Ici 0) := by
        refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont.continuousOn
          hdiff.differentiableOn (fun x hx => ?_)
        rw [interior_Ici] at hx
        rw [(hderiv x).deriv]
        have hx' : 0 < x := hx
        have := hpos x; have := hden x
        rw [neg_nonpos]; positivity
      have := hanti (self_mem_Ici) hv hv
      rw [h0] at this; exact this
    · have hmono : MonotoneOn h (Iic 0) := by
        refine monotoneOn_of_deriv_nonneg (convex_Iic 0) hcont.continuousOn
          hdiff.differentiableOn (fun x hx => ?_)
        rw [interior_Iic] at hx
        rw [(hderiv x).deriv]
        have hx' : x < 0 := hx
        have h1 := hpos x; have h2 := hden x
        rw [le_neg, neg_zero, div_nonpos_iff]
        right
        refine ⟨?_, h2.le⟩
        have hx0 : 0 < -x := by linarith
        have hq : 0 < 2 * π * (-x) * (3 * a ^ 2 + 4 * a * x + 2 * x ^ 2) :=
          mul_pos (mul_pos (by positivity) hx0) h1
        linarith
      have := hmono hv (self_mem_Iic) hv
      rw [h0] at this; exact this
  simp only [hh, Complex.log_im] at hle
  linarith

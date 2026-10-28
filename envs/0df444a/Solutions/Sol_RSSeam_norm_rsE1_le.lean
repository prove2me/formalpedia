-- Prove2me | solution 1 for RSSeam.norm_rsE1_le
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:22:35.383544+00:00
-- url     : https://prove2.me/submissions/d6bb8d7f-ec91-46b8-accc-e1a22dfd8ab8

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_integral_sq_mul_exp_neg_mul_sq
import Theorems.Thm_RSSeam_norm_E1_integrand_far
import Theorems.Thm_RSSeam_norm_E1_integrand_near
namespace RSInt
end RSInt
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

theorem integrable_sq_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : ℝ => v ^ 2 * Real.exp (-b * v ^ 2)) := by
  have := integrable_rpow_mul_exp_neg_mul_sq hb (s := 2) (by norm_num)
  simpa only [Real.rpow_two] using this

/-! ## 5. The tau = 2 Mordell integral is uniformly bounded -/











/-! ## 6. The error integral `rsE1` is `O(1/a)` -/

















/-! ## 7. The explicit C0 remainder bound -/













end RSInt

end

/-  RSSeam_B3Bound.lean -- lane SEAM: the C0-corrected Riemann-Siegel remainder bound with a LOWER
    starting height, t >= 509 (saddle variable a = sqrt(t/2pi) >= 9) instead of t >= 10000 (a >= 39).
    Imports `RS_B3Bound` read-only and reuses its lemmas; nothing in lane RS is edited.

    ## The headlines (no `sorry`, no `native_decide`, no new axioms)

      `rs_remainder_C0_alpha_seam` : for t >= 509, 0 < p = rsFrac t, cos(2 pi p) ≠ 0, and every phase
      phi with |phi - rsThetaMain t| <= 1/t,
          |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) a^(-1/2) Psi(p)| <= (13/20) a^(-3/2).
      `rs_remainder_C0_seam` : the same in t,
          |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) (t/2pi)^(-1/4) Psi(p)| <= (13/5) t^(-3/4).

    ## What changed against `RS_B3Bound` (the error budget re-run at a >= 9)

      * near/far split of the error integral at |v| = a/3 (was a/9); near the saddle the amplitude
        bound |rsPhi - 1| <= e e^e still applies because |w| = sqrt 2 |v| <= a/2;
      * near: e <= |w| (13/25 + 17/4 |w|^2)/a and e <= 27/5 v^2 + 1/600, so the integrand is
        <= e^{1/600}/(pi a) (13/25 + 17/2 v^2) e^{-7 v^2};
      * far: |integrand| <= 5 e^{-pi a^2/18} e^{-pi v^2/2}, and e^{-x} <= 8!/x^8 at x >= 14;
      * |rsE1 a p| <= (49/200 + 1/200)/a = (1/4)/a for a >= 9 (was (9/50)/a for a >= 39);
      * |rsJ p| <= 4 (unchanged, `RSInt.norm_rsJ_le`); phase term 8|delta| <= 4/(pi a^2) <= (3/20)/a;
      * budget 2 (1/4) + 3/20 = 13/20 in the a-form; (2 pi)^(3/4) <= 4 gives 13/5 in t.

    Untrusted numerics (scratchpad/seam/remainder.py): the true C0-corrected remainder is
    <= 0.121 t^(-3/4) on samples in [200, 10100]; so 13/5 is honest with a ~20x margin.

    conjecture1_proved = False.  An explicit finite-height remainder inequality; nothing here bears on
    the Riemann Hypothesis.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

section
namespace RSSeam
end RSSeam
open RSSeam

open RSInt






theorem solution {a p : ℝ} (ha : 9 ≤ a) :
    ‖rsE1 a p‖ ≤ Real.exp (1 / 600) / (π * a) * (13 / 25) * Real.sqrt (π / 7) +
      Real.exp (1 / 600) / (π * a) * (17 / 2) * (Real.sqrt (π / 7) / (2 * 7)) +
      5 * Real.exp (-(π * a ^ 2 / 18)) * Real.sqrt (π / (π / 2)) := by
  have ha0 : 0 < a := by linarith
  set K₁ := Real.exp (1 / 600) / (π * a) with hK₁
  set K₂ := 5 * Real.exp (-(π * a ^ 2 / 18)) with hK₂
  have hi1 : Integrable (fun v : ℝ => Real.exp (-7 * v ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have hi2 : Integrable (fun v : ℝ => v ^ 2 * Real.exp (-7 * v ^ 2)) :=
    integrable_sq_mul_exp_neg_mul_sq (by norm_num)
  have hi3 : Integrable (fun v : ℝ => Real.exp (-(π / 2) * v ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  have hint : Integrable (fun v : ℝ => K₁ * (13 / 25) * Real.exp (-7 * v ^ 2) +
      K₁ * (17 / 2) * (v ^ 2 * Real.exp (-7 * v ^ 2)) + K₂ * Real.exp (-(π / 2) * v ^ 2)) :=
    ((hi1.const_mul _).add (hi2.const_mul _)).add (hi3.const_mul _)
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₂0 : 0 ≤ K₂ := by positivity
  have hpt : ∀ v : ℝ, ‖cexp (2 * ↑π * I * ((v : ℂ) * (1 + I)) ^ 2) /
      rsD (p + (v : ℂ) * (1 + I)) * (rsPhi a ((v : ℂ) * (1 + I)) - 1) * (1 + I)‖ ≤
      K₁ * (13 / 25) * Real.exp (-7 * v ^ 2) +
        K₁ * (17 / 2) * (v ^ 2 * Real.exp (-7 * v ^ 2)) + K₂ * Real.exp (-(π / 2) * v ^ 2) := by
    intro v
    have h1 : 0 ≤ K₁ * (13 / 25) * Real.exp (-7 * v ^ 2) +
        K₁ * (17 / 2) * (v ^ 2 * Real.exp (-7 * v ^ 2)) := by positivity
    have h2 : 0 ≤ K₂ * Real.exp (-(π / 2) * v ^ 2) := by positivity
    rcases le_total |v| (a / 3) with hv | hv
    · have := norm_E1_integrand_near (p := p) ha hv
      have e : K₁ * (13 / 25 + 17 / 2 * v ^ 2) * Real.exp (-7 * v ^ 2) =
          K₁ * (13 / 25) * Real.exp (-7 * v ^ 2) +
            K₁ * (17 / 2) * (v ^ 2 * Real.exp (-7 * v ^ 2)) := by ring
      rw [← hK₁, e] at this
      linarith
    · have := norm_E1_integrand_far (p := p) ha hv
      rw [← hK₂] at this
      linarith
  have hA : Integrable (fun v : ℝ => K₁ * (13 / 25) * Real.exp (-7 * v ^ 2) +
      K₁ * (17 / 2) * (v ^ 2 * Real.exp (-7 * v ^ 2))) := (hi1.const_mul _).add (hi2.const_mul _)
  have hB1 : Integrable (fun v : ℝ => K₁ * (13 / 25) * Real.exp (-7 * v ^ 2)) := hi1.const_mul _
  have hB2 : Integrable (fun v : ℝ => K₁ * (17 / 2) * (v ^ 2 * Real.exp (-7 * v ^ 2))) :=
    hi2.const_mul _
  have hB3 : Integrable (fun v : ℝ => K₂ * Real.exp (-(π / 2) * v ^ 2)) := hi3.const_mul _
  unfold rsE1 lineUp
  simp only [ofReal_zero, zero_add]
  refine le_trans (norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)) (le_of_eq ?_)
  rw [integral_add hA hB3, integral_add hB1 hB2, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_gaussian, integral_sq_mul_exp_neg_mul_sq (by norm_num),
    integral_gaussian]

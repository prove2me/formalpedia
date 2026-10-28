-- Prove2me | solution 1 for RSSeam.norm_E1_integrand_near
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:12:54.635073+00:00
-- url     : https://prove2.me/submissions/42b32284-1db4-4423-92e8-944971680303

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_norm_rsPhi_sub_one_le
namespace RSInt
end RSInt
/-  RS_Strip.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 1:
    contour tools.

    Mathlib-only (no corpus import), so the file can serve the dbn island's M5 layer L6 as well.

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `integrable_exp_quad`, `integrable_of_continuous_of_tail` : integrability of a continuous
        function from a Gaussian-type tail bound `C exp(-a v^2 + b |v|)`.
      * `strip_integral_eq` : Cauchy's theorem on a HORIZONTAL STRIP y1 <= Im z <= y2 with decay at
        both ends: the integrals along the two edges agree.  (Mathlib's rectangle theorem
        `integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn` plus two limits.)
      * `lineUp c F`, `lineDn c F` : the oriented integrals along the slanted lines through the real
        point `c` with directions `1 + I` (slope +1) and `1 - I` (slope -1).
      * `lineUp_eq_of_strip`, `lineDn_eq_of_strip` : line independence -- the integral along the line
        through `c1` equals the one through `c2` when `F` is continuous on the closed slanted strip,
        holomorphic inside, and tends to 0 at infinity in the strip.

    conjecture1_proved = False.  Contour-integration infrastructure; nothing here bears on RH.
-/


open Complex MeasureTheory Filter Topology Set

noncomputable section

namespace RSInt

/-! ## 1. Integrability from a Gaussian tail -/







/-! ## 2. Cauchy's theorem on a horizontal strip -/



/-! ## 3. Slanted lines -/



















theorem norm_one_add_I : ‖(1 + I : ℂ)‖ = Real.sqrt 2 := by
  rw [Complex.norm_def, Complex.normSq_apply]; simp; norm_num







end RSInt

end

/-  RS_Kernel.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 2:
    Riemann's kernels, their difference equations, Gaussian bounds, the Fresnel line integral,
    the pole-crossing lemmas and the Mordell closed form.

    Mathlib-only (imports `RS_Strip` only).

    ## The kernels

        rsD x = e^{i pi x} - e^{-i pi x}          (= 2 i sin(pi x); zeros exactly at the integers)
        rsG x = e^{ i pi x^2} / rsD x              (Riemann's kernel of the zeta integral)
        rsH x = e^{-i pi x^2} / rsD x              (the kernel of the chi-side integral)

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `rsD_eq_zero_iff`, `rsD_add_one`, `rsG_add_one`, `rsH_add_one` : zeros and the difference
        equations  rsG(x+1) = rsG x + e^{i pi (x^2+x)},  rsH(x+1) = rsH x - e^{-i pi (x^2+x)}.
      * `norm_rsG_le`, `norm_rsH_le` : on a slanted strip, away from the real axis (|Im x| >= 1), the
        kernels are bounded by exp(-2 pi (Im x)^2 + 2 pi D |Im x|)  (Gaussian decay).
      * `lineUp_fresnel`, `lineUp_gauss` : the Gaussian line integrals, e.g.
            lineUp c (x |-> e^{i pi (x^2+x) - x y}) = e^{y/2 + i y^2/(4 pi)}     (every c, every y).
      * `lineUp_same_gap`, `lineUp_cross` : moving the slope-(+1) line inside a gap (n, n+1) changes
        nothing; moving it across the pole at the integer n adds phi(n):
            lineUp c2 (rsG * phi) = lineUp c1 (rsG * phi) + phi n,   n-1 < c1 < n < c2 < n+1,
        for every phi holomorphic on the strip with at most exponential growth.  No residue theorem
        is used: the pole is removed by `dslope`, and the jump of the bare kernel is computed from
        the difference equation and the Fresnel integral.
      * `lineDn_same_gap`, `lineDn_cross` : the slope-(-1) analogues for rsH (by conjugation).
      * `lineUp_mordell` : the Mordell closed form, for 0 < c < 1 and every y:
            lineUp c (x |-> rsG x e^{-x y}) (e^{-y/2} - e^{y/2}) = e^{-y/2} - e^{i y^2/(4 pi)}.

    conjecture1_proved = False.  Contour identities for one explicit kernel; nothing here bears
    on RH.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

namespace RSInt

/-! ## 1. The kernels and their algebra -/



























/-! ## 2. Norm bounds -/





theorem norm_exp_piI (x : ℂ) : ‖cexp (↑π * I * x)‖ = Real.exp (-(π * x.im)) := by
  rw [Complex.norm_exp]; congr 1; simp [mul_re, mul_im]

theorem norm_exp_neg_piI (x : ℂ) : ‖cexp (-(↑π * I * x))‖ = Real.exp (π * x.im) := by
  rw [Complex.norm_exp]; congr 1; simp [mul_re, mul_im]

theorem norm_rsD_ge (x : ℂ) :
    Real.exp (π * |x.im|) - Real.exp (-(π * |x.im|)) ≤ ‖rsD x‖ := by
  unfold rsD
  rcases le_total 0 x.im with h | h
  · rw [abs_of_nonneg h]
    have := norm_sub_norm_le (cexp (-(↑π * I * x))) (cexp (↑π * I * x))
    rw [norm_exp_piI, norm_exp_neg_piI, norm_sub_rev] at this
    linarith
  · rw [abs_of_nonpos h, mul_neg, neg_neg]
    have := norm_sub_norm_le (cexp (↑π * I * x)) (cexp (-(↑π * I * x)))
    rw [norm_exp_piI, norm_exp_neg_piI] at this
    linarith















/-! ## 3. The Fresnel line integral -/











/-! ## 4. Gaussian tails, line integrability, and the strip wrappers -/























/-! ## 5. Linearity and translation of line integrals -/













/-! ## 6. Holomorphy of the kernels off the integers -/













/-! ## 7. The Fresnel/Gaussian integrands are integrable along the lines -/









/-! ## 8. Moving the line inside a gap, and across a pole -/











/-! ## 9. The slope-(-1) side by conjugation -/

















/-! ## 10. The Mordell closed form -/



end RSInt

end

/-  RS_Mellin.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 3:
    the Mellin step.  Mathlib-only (imports `RS_Kernel`).

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `integral_cpow_mul_exp_neg_mul_Ioi_complex` : the complex-scaled Gamma integral
            int_0^oo rho^(s-1) e^(-z rho) d rho = (1/z)^s Gamma(s),     Re s > 0, Re z > 0,
        extending Mathlib's real-`z` lemma by the identity theorem.
      * `one_div_mul_cpow` : the branch bookkeeping (1/(x(1+i)))^s = x^(-s) (1+i)^(-s) whenever
        Re(x(1+i)) > 0.
      * `mellin_step` : Fubini on (line) x (0, oo):
            Gamma(s) lineUp c (rsG x^(-s)) = (1+i)^s int_0^oo rho^(s-1) rsK c ((1+i) rho) d rho,
        with rsK c y = lineUp c (rsG e^(-x y)) the Mordell integral.
      * `rsK_split` : the Mordell closed form at y = (1+i) rho, split into the Bose kernel and the
        Gaussian (chi-side) kernel.
      * `integral_bose` : int_0^oo rho^(s-1) / (e^((1+i) rho) - 1) = (1+i)^(-s) Gamma(s) zeta(s),
        Re s > 1 (geometric series, termwise integration, Mathlib's Dirichlet series for zeta).
      * `integral_Epart` : the chi-side kernel integral equals (2 pi)^s (1-i)^(-s) rsHR s, where
        rsHR s = int_0^oo rsH(r(1-i)) (r(1-i))^(s-1) (1-i) dr is half of the chi-side line.
      * `mellin_identity` : for Re s > 1 and 0 < c < 1,
            Gamma(s) lineUp c (rsG x^(-s)) = -Gamma(s) zeta(s) + (2 pi)^s (1+i)^s (1-i)^(-s) rsHR s.

    conjecture1_proved = False.  Classical integral identities for zeta; nothing here bears on RH.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

namespace RSInt

/-! ## 1. Integrability of `rho^a e^(-b rho)` and norms -/









/-! ## 2. Branch bookkeeping -/







/-! ## 3. The complex-scaled Gamma integral -/



/-! ## 4. The Mellin step (Fubini) -/













/-! ## 5. Splitting the Mordell kernel -/







/-! ## 6. The Bose integral -/





/-! ## 7. The chi-side kernel -/













/-! ## 8. Integrability of the two pieces on (0, oo) -/

theorem le_exp_sub_exp {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ρ ≤ Real.exp (ρ / 2) - Real.exp (-(ρ / 2)) := by
  have h := Real.self_le_sinh_iff.mpr (by linarith : 0 ≤ ρ / 2)
  rw [Real.sinh_eq] at h
  linarith









/-! ## 9. The Mellin identity -/



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

namespace RSInt

/-! ## 1. The second Gaussian moment -/





/-! ## 2. Lower bound for the denominator -/

theorem norm_rsD_ge_two_pi_im (z : ℂ) : 2 * π * |z.im| ≤ ‖rsD z‖ := by
  have h1 := norm_rsD_ge z
  have h2 := le_exp_sub_exp (ρ := 2 * π * |z.im|) (by positivity)
  rw [show 2 * π * |z.im| / 2 = π * |z.im| by ring] at h2
  linarith

/-! ## 3. The amplitude near the saddle point -/







/-! ## 4. The saddle point is a global maximum along the steepest-descent line -/









/-! ## 4b. Integrability of the second Gaussian moment -/



/-! ## 5. The tau = 2 Mordell integral is uniformly bounded -/











/-! ## 6. The error integral `rsE1` is `O(1/a)` -/

theorem norm_w_eq (v : ℝ) : ‖(v : ℂ) * (1 + I)‖ = Real.sqrt 2 * |v| := by
  rw [norm_mul, Complex.norm_real, norm_one_add_I, Real.norm_eq_abs, mul_comm]

theorem sqrt_two_le_three_halves : Real.sqrt 2 ≤ 3 / 2 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]



theorem norm_exp_gauss_diag (v : ℝ) :
    ‖cexp (2 * ↑π * I * ((v : ℂ) * (1 + I)) ^ 2)‖ = Real.exp (-(4 * π) * v ^ 2) := by
  rw [Complex.norm_exp]; congr 1; simp [pow_two, mul_re, mul_im]; ring









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


theorem solution {a p v : ℝ} (ha : 9 ≤ a) (hv : |v| ≤ a / 3) :
    ‖cexp (2 * ↑π * I * ((v : ℂ) * (1 + I)) ^ 2) / rsD (p + (v : ℂ) * (1 + I)) *
        (rsPhi a ((v : ℂ) * (1 + I)) - 1) * (1 + I)‖ ≤
      Real.exp (1 / 600) / (π * a) * (13 / 25 + 17 / 2 * v ^ 2) * Real.exp (-7 * v ^ 2) := by
  have ha0 : 0 < a := by linarith
  have hRHS : 0 ≤ Real.exp (1 / 600) / (π * a) * (13 / 25 + 17 / 2 * v ^ 2) *
      Real.exp (-7 * v ^ 2) := by positivity
  rcases eq_or_ne v 0 with rfl | hv0
  · have h0 : rsPhi a ((0 : ℝ) * (1 + I) : ℂ) = 1 := by simp [rsPhi]
    rw [h0, sub_self, mul_zero, zero_mul, norm_zero]
    exact hRHS
  set w : ℂ := (v : ℂ) * (1 + I) with hwdef
  set n : ℝ := ‖w‖ with hn
  have hnv : n = Real.sqrt 2 * |v| := norm_w_eq v
  have hn2 : n ^ 2 = 2 * v ^ 2 := by
    rw [hnv, mul_pow, Real.sq_sqrt (by norm_num), sq_abs]
  have hn0 : 0 ≤ n := norm_nonneg _
  have hna : n ≤ a / 2 := by
    rw [hnv]
    calc Real.sqrt 2 * |v| ≤ 3 / 2 * (a / 3) :=
          mul_le_mul sqrt_two_le_three_halves hv (abs_nonneg _) (by norm_num)
      _ = a / 2 := by ring
  have hphi := norm_rsPhi_sub_one_le ha0 (show ‖w‖ ≤ a / 2 by rw [← hn]; exact hna)
  rw [← hn] at hphi
  set ε := n / (2 * a) + n ^ 2 / (2 * a ^ 2) + 4 * π / 3 * n ^ 3 / a with hε
  have hε1 : ε ≤ n * ((13 / 25 + 17 / 2 * v ^ 2) / a) := by
    have hv2 : 17 / 2 * v ^ 2 = 17 / 4 * n ^ 2 := by rw [hn2]; ring
    rw [hv2]
    have e : n * ((13 / 25 + 17 / 4 * n ^ 2) / a) - ε =
        n / a * (1 / 50 + (17 / 4 - 4 * π / 3) * n ^ 2 - n / (2 * a)) := by
      rw [hε]; field_simp; ring
    have h1 : n / (2 * a) ≤ n / 18 :=
      div_le_div_of_nonneg_left hn0 (by norm_num) (by linarith)
    have h2 : (1 / 20 : ℝ) ≤ 17 / 4 - 4 * π / 3 := by linarith [Real.pi_lt_d2]
    have h3 : 0 ≤ 1 / 50 + 1 / 20 * n ^ 2 - n / 18 := by nlinarith [sq_nonneg (n - 5 / 9)]
    have h4 : 1 / 20 * n ^ 2 ≤ (17 / 4 - 4 * π / 3) * n ^ 2 :=
      mul_le_mul_of_nonneg_right h2 (sq_nonneg n)
    have h5 : 0 ≤ n / a * (1 / 50 + (17 / 4 - 4 * π / 3) * n ^ 2 - n / (2 * a)) :=
      mul_nonneg (div_nonneg hn0 ha0.le) (by linarith)
    linarith
  have hε2 : ε ≤ 27 / 5 * v ^ 2 + 1 / 600 := by
    have h1 : n / (2 * a) ≤ n / 18 :=
      div_le_div_of_nonneg_left hn0 (by norm_num) (by linarith)
    have e1 : n / (2 * a) ≤ n ^ 2 / 2 + 1 / 648 := by nlinarith [sq_nonneg (n - 1 / 18)]
    have e2 : n ^ 2 / (2 * a ^ 2) ≤ n ^ 2 / 162 :=
      div_le_div_of_nonneg_left (sq_nonneg n) (by norm_num) (by nlinarith)
    have e3 : 4 * π / 3 * n ^ 3 / a ≤ 4 * π / 3 * n ^ 2 / 2 := by
      have h : n ^ 3 / a ≤ n ^ 2 / 2 := by
        rw [div_le_div_iff₀ ha0 (by norm_num)]
        have e : n ^ 3 * 2 = n ^ 2 * (2 * n) := by ring
        rw [e]; exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg n)
      calc 4 * π / 3 * n ^ 3 / a = 4 * π / 3 * (n ^ 3 / a) := by ring
        _ ≤ 4 * π / 3 * (n ^ 2 / 2) := mul_le_mul_of_nonneg_left h (by positivity)
        _ = 4 * π / 3 * n ^ 2 / 2 := by ring
    have e4 : 4 * π / 3 * n ^ 2 / 2 ≤ 21 / 10 * n ^ 2 := by
      nlinarith [sq_nonneg n, Real.pi_lt_d2]
    rw [hε]
    have e5 : n ^ 2 / 2 + n ^ 2 / 162 + 21 / 10 * n ^ 2 ≤ 27 / 10 * n ^ 2 := by
      nlinarith [sq_nonneg n]
    have e6 : 27 / 10 * n ^ 2 = 27 / 5 * v ^ 2 := by rw [hn2]; ring
    linarith
  have hexpw : ‖cexp (2 * ↑π * I * w ^ 2)‖ = Real.exp (-(4 * π) * v ^ 2) := norm_exp_gauss_diag v
  have him : ((p : ℂ) + w).im = v := by simp [hwdef]
  have hD : 2 * π * |v| ≤ ‖rsD (p + w)‖ := by
    have := norm_rsD_ge_two_pi_im (p + w); rwa [him] at this
  have hvpos : 0 < |v| := abs_pos.mpr hv0
  have hDpos : 0 < 2 * π * |v| := by positivity
  have hΦ : ‖rsPhi a w - 1‖ ≤
      n * ((13 / 25 + 17 / 2 * v ^ 2) / a) * Real.exp (27 / 5 * v ^ 2 + 1 / 600) :=
    hphi.trans (mul_le_mul hε1 (Real.exp_le_exp.mpr hε2) (Real.exp_pos _).le (by positivity))
  have hexp2 : Real.exp (-(4 * π) * v ^ 2) * Real.exp (27 / 5 * v ^ 2 + 1 / 600) =
      Real.exp (1 / 600) * Real.exp (-(4 * π - 27 / 5) * v ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  calc ‖cexp (2 * ↑π * I * w ^ 2) / rsD (p + w) * (rsPhi a w - 1) * (1 + I)‖
      = Real.exp (-(4 * π) * v ^ 2) * ‖rsPhi a w - 1‖ * Real.sqrt 2 / ‖rsD (p + w)‖ := by
        rw [norm_mul, norm_mul, norm_div, hexpw, norm_one_add_I]; ring
    _ ≤ Real.exp (-(4 * π) * v ^ 2) * (n * ((13 / 25 + 17 / 2 * v ^ 2) / a) *
          Real.exp (27 / 5 * v ^ 2 + 1 / 600)) * Real.sqrt 2 / (2 * π * |v|) := by
        gcongr
    _ = (Real.exp (-(4 * π) * v ^ 2) * Real.exp (27 / 5 * v ^ 2 + 1 / 600)) *
          (Real.sqrt 2 * Real.sqrt 2) * (13 / 25 + 17 / 2 * v ^ 2) / (2 * π * a) *
          (|v| / |v|) := by
        rw [hnv]; field_simp
    _ = Real.exp (1 / 600) / (π * a) * (13 / 25 + 17 / 2 * v ^ 2) *
          Real.exp (-(4 * π - 27 / 5) * v ^ 2) := by
        rw [hexp2, hss, div_self hvpos.ne']; field_simp
    _ ≤ Real.exp (1 / 600) / (π * a) * (13 / 25 + 17 / 2 * v ^ 2) * Real.exp (-7 * v ^ 2) := by
        gcongr
        nlinarith [Real.pi_gt_d2, sq_nonneg v]

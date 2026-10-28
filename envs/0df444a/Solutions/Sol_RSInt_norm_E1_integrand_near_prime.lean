-- Prove2me | solution 1 for RSInt.norm_E1_integrand_near_prime
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:08:15.873712+00:00
-- url     : https://prove2.me/submissions/02f88e9e-0ec8-49ca-9eab-deba5a4bc2b9

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_B3Sharp
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_near_eta_le_lin
import Theorems.Thm_RSInt_near_eta_le_sq
import Theorems.Thm_RSInt_norm_rsPhi_sub_one_le_prime
import Theorems.Thm_RSInt_rsEone_line
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

/-  RS_B3Sharp.lean -- lane RS, brick B3 SHARPENED (RSC0 Phase 2): the same C0-corrected
    Riemann-Siegel remainder as `RS_B3Bound` / `RSSeam_B3Bound`, with smaller kernel-checked constants.
    New theorems only; imports `RSSeam_B3Bound` (hence `RS_B3Bound`) read-only and edits nothing.

    ## The headlines (no `sorry`, no `native_decide`, no new axioms)

      `RSInt.rs_remainder_C0_alpha'` : for t >= 4250 (a = sqrt(t/2pi) >= 26), 0 < p = rsFrac t,
      cos(2 pi p) ≠ 0, and every phase phi with |phi - rsThetaMain t| <= 1/t,
          |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) a^(-1/2) Psi(p)| <= (3/20) a^(-3/2);
      `RSInt.rs_remainder_C0'` : the same in t, <= (3/5) t^(-3/4).
      `RSSeam.rs_remainder_C0_alpha_seam'` : for t >= 509, <= (21/100) a^(-3/2);
      `RSSeam.rs_remainder_C0_seam'` : the same in t, <= (21/25) t^(-3/4).
      The old statements (2/5 and 2 at t >= 10000; 13/20 and 13/5 at t >= 509) are re-derived from
      the new ones as `*_of_sharp` corollaries at the end of the file.

    ## What is sharper than `RS_B3Bound` (same architecture, elementary steps)

      * the saddle exponent E is split as E = E1 + E2 with E1 = -2 pi i w^3/(3a) - w/(2a) EXACT and
        |E2| <= pi |w|^4/a^2 + |w|^2/(2a^2) (Mathlib's log-Taylor remainders of orders 4 and 2), and
        |e^E - 1| <= |E| + |E|^2 e^{|E|} (`norm_rsPhi_sub_one_le'`);
      * on the steepest-descent line |E1| = (sqrt2/2)|v| |1 - 8 pi v^2/3| / a EXACTLY (`rsEone_line`):
        the linear and cubic terms have OPPOSITE signs, and |1 - x| <= 41/40 - (5/4)x + (5/8)x^2;
        the main term then integrates against the FULL Gaussian e^{-4 pi v^2} to (49/120)/(2 pi a);
      * only the second-order remainder pays for e^{|E|}, with e^{-(4 pi - 37/10) v^2};
      * absolute Gaussian moments int |v|^j e^{-b v^2} = b^{-(j+1)/2} Gamma((j+1)/2) (`gaussMom_eq`);
      * one near-zone lemma (|v| <= a/3) for every a >= a0 >= 9, the far zone reused verbatim from
        `RSSeam.norm_E1_integrand_far`;
      * |rsJ p| <= 4/5 by completing the square on the midline (was 4) (`norm_rsJ_le'`).
      Budget: |rsE1| <= (7/100)/a (a >= 26) and (9/100)/a (a >= 9); phase 4/(5 pi a^2) <= (1/100)/a
      resp. (3/100)/a; 2 (7/100) + 1/100 = 3/20 and 2 (9/100) + 3/100 = 21/100; (2 pi)^(3/4) <= 4.

    The numeric lemmas bound a|rsE1| by 0.0689 (a >= 26) and 0.0821 (a >= 9).  Untrusted design
    numerics (closed forms 0.0688 and 0.0770): ~/rh-team/rsc0/out/phase2/lean_numerics.py.

    Not yet `lean_lib`s (lakefile.toml untouched): compile with `lake env lean`; a landing PR adds
    append-only `[[lean_lib]]` entries for RS_B3Sharp and RS_BridgeSharp (and RS_AxiomGuardSharp).

    conjecture1_proved = False.  An explicit finite-height remainder inequality; nothing here bears on
    the Riemann Hypothesis.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

namespace RSInt

/-! ## 1. Absolute Gaussian moments -/





































/-! ## 2. The saddle exponent split into its exact linear-plus-cubic part and a remainder -/











/-! ## 3. The near-zone majorant (|v| <= a/3, every a >= a0 >= 9) -/











theorem sum_cMain (r : ℝ) :
    ∑ j ∈ Finset.range 5, cMain j * r ^ j = 41 / 40 - 10 * π / 3 * r ^ 2 + 40 * π ^ 2 / 9 * r ^ 4 := by
  simp [Finset.sum_range_succ, cMain]
  ring

theorem sum_cEtwo (r : ℝ) : ∑ j ∈ Finset.range 4, cEtwo j * r ^ j = r + 4 * π * r ^ 3 := by
  simp [Finset.sum_range_succ, cEtwo]

theorem sum_cS (a0 r : ℝ) :
    ∑ j ∈ Finset.range 8, cS a0 j * r ^ j =
      r * (Real.sqrt 2 / 2 * (1 + 8 * π / 3 * r ^ 2) + (r + 4 * π * r ^ 3) / a0) ^ 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp [Finset.sum_range_succ, cS]
  linear_combination (-(r * (1 + 8 * π / 3 * r ^ 2) ^ 2 / 4)) * hs

theorem qMain_nonneg (r : ℝ) : 0 ≤ 41 / 40 - 10 * π / 3 * r ^ 2 + 40 * π ^ 2 / 9 * r ^ 4 := by
  nlinarith [sq_nonneg (π * r ^ 2 - 3 / 8), Real.pi_pos]

theorem abs_one_sub_le_quad (x : ℝ) : |1 - x| ≤ 41 / 40 - 5 / 4 * x + 5 / 8 * x ^ 2 := by
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x - 1 / 5), sq_nonneg (x - 9 / 5)]









/-- The three algebraic identities/inequalities that assemble the pointwise bound. -/
theorem near_T1 {a r y Q G : ℝ} (ha : 0 < a) (hr : 0 < r) (hG : 0 ≤ G) (hyQ : y ≤ Q) :
    G * (Real.sqrt 2 / 2 * r * y / a) * Real.sqrt 2 / (2 * π * r) ≤ 1 / (2 * π * a) * (Q * G) := by
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have e : G * (Real.sqrt 2 / 2 * r * y / a) * Real.sqrt 2 / (2 * π * r) =
      1 / (2 * π * a) * (y * G) * ((Real.sqrt 2 * Real.sqrt 2) / 2) := by
    field_simp
  rw [e, hss, div_self two_ne_zero, mul_one]
  have : 0 ≤ 1 / (2 * π * a) := by positivity
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hyQ hG) this

theorem near_T2 {a v G : ℝ} (ha : 0 < a) (hv : v ≠ 0) :
    G * (π * (4 * v ^ 4) / a ^ 2 + 2 * v ^ 2 / (2 * a ^ 2)) * Real.sqrt 2 / (2 * π * |v|) =
      Real.sqrt 2 / (2 * π * a ^ 2) * ((|v| + 4 * π * |v| ^ 3) * G) := by
  have hvpos : 0 < |v| := abs_pos.mpr hv
  have h4abs : |v| ^ 4 = v ^ 4 := by
    rw [show |v| ^ 4 = (|v| ^ 2) ^ 2 by ring, sq_abs]; ring
  rw [← sq_abs v, ← h4abs]
  field_simp
  ring

theorem near_T3 {a a0 r v η P G : ℝ} (ha : 0 < a) (hr : 0 < r) (hG : 0 ≤ G) (hη0 : 0 ≤ η)
    (hη1 : η ≤ r * P / a) (hηe : Real.exp η ≤ Real.exp (1 / (2 * a0 ^ 2)) * Real.exp (37 / 10 * v ^ 2))
    (hGe : G * Real.exp (37 / 10 * v ^ 2) = Real.exp (-(4 * π - 37 / 10) * v ^ 2)) :
    G * (η ^ 2 * Real.exp η) * Real.sqrt 2 / (2 * π * r) ≤
      Real.sqrt 2 * Real.exp (1 / (2 * a0 ^ 2)) / (2 * π * a ^ 2) *
        (r * P ^ 2 * Real.exp (-(4 * π - 37 / 10) * v ^ 2)) := by
  have hsq : η ^ 2 ≤ (r * P / a) ^ 2 := pow_le_pow_left₀ hη0 hη1 2
  have hR3 : η ^ 2 * Real.exp η ≤
      (r * P / a) ^ 2 * (Real.exp (1 / (2 * a0 ^ 2)) * Real.exp (37 / 10 * v ^ 2)) :=
    mul_le_mul hsq hηe (Real.exp_pos _).le (sq_nonneg _)
  have hD : 0 < 2 * π * r := by positivity
  calc G * (η ^ 2 * Real.exp η) * Real.sqrt 2 / (2 * π * r)
      ≤ G * ((r * P / a) ^ 2 * (Real.exp (1 / (2 * a0 ^ 2)) * Real.exp (37 / 10 * v ^ 2))) *
          Real.sqrt 2 / (2 * π * r) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hR3 hG) (Real.sqrt_nonneg 2)) hD.le
    _ = Real.sqrt 2 * Real.exp (1 / (2 * a0 ^ 2)) / (2 * π * a ^ 2) *
          (r * P ^ 2 * (G * Real.exp (37 / 10 * v ^ 2))) := by
        field_simp
    _ = _ := by rw [hGe]



/-! ## 4. The error integral, sharpened -/











/-! ## 5. Numerics -/





























/-! ## 6. The tau = 2 Mordell integral: `|rsJ p| <= 4/5` (completing the square on the midline) -/





/-! ## 7. The sharpened C0 remainder bound, `a >= 26` (t >= 4250) -/







/-! ## 8. The old headlines re-derived from the sharpened ones -/





end RSInt

namespace RSSeam

open RSInt

/-! ## 9. The seam, sharpened: t >= 509 (a >= 9) -/









end RSSeam

end

/-  RS_B3Sharp.lean -- lane RS, brick B3 SHARPENED (RSC0 Phase 2): the same C0-corrected
    Riemann-Siegel remainder as `RS_B3Bound` / `RSSeam_B3Bound`, with smaller kernel-checked constants.
    New theorems only; imports `RSSeam_B3Bound` (hence `RS_B3Bound`) read-only and edits nothing.

    ## The headlines (no `sorry`, no `native_decide`, no new axioms)

      `RSInt.rs_remainder_C0_alpha'` : for t >= 4250 (a = sqrt(t/2pi) >= 26), 0 < p = rsFrac t,
      cos(2 pi p) ≠ 0, and every phase phi with |phi - rsThetaMain t| <= 1/t,
          |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) a^(-1/2) Psi(p)| <= (3/20) a^(-3/2);
      `RSInt.rs_remainder_C0'` : the same in t, <= (3/5) t^(-3/4).
      `RSSeam.rs_remainder_C0_alpha_seam'` : for t >= 509, <= (21/100) a^(-3/2);
      `RSSeam.rs_remainder_C0_seam'` : the same in t, <= (21/25) t^(-3/4).
      The old statements (2/5 and 2 at t >= 10000; 13/20 and 13/5 at t >= 509) are re-derived from
      the new ones as `*_of_sharp` corollaries at the end of the file.

    ## What is sharper than `RS_B3Bound` (same architecture, elementary steps)

      * the saddle exponent E is split as E = E1 + E2 with E1 = -2 pi i w^3/(3a) - w/(2a) EXACT and
        |E2| <= pi |w|^4/a^2 + |w|^2/(2a^2) (Mathlib's log-Taylor remainders of orders 4 and 2), and
        |e^E - 1| <= |E| + |E|^2 e^{|E|} (`norm_rsPhi_sub_one_le'`);
      * on the steepest-descent line |E1| = (sqrt2/2)|v| |1 - 8 pi v^2/3| / a EXACTLY (`rsEone_line`):
        the linear and cubic terms have OPPOSITE signs, and |1 - x| <= 41/40 - (5/4)x + (5/8)x^2;
        the main term then integrates against the FULL Gaussian e^{-4 pi v^2} to (49/120)/(2 pi a);
      * only the second-order remainder pays for e^{|E|}, with e^{-(4 pi - 37/10) v^2};
      * absolute Gaussian moments int |v|^j e^{-b v^2} = b^{-(j+1)/2} Gamma((j+1)/2) (`gaussMom_eq`);
      * one near-zone lemma (|v| <= a/3) for every a >= a0 >= 9, the far zone reused verbatim from
        `RSSeam.norm_E1_integrand_far`;
      * |rsJ p| <= 4/5 by completing the square on the midline (was 4) (`norm_rsJ_le'`).
      Budget: |rsE1| <= (7/100)/a (a >= 26) and (9/100)/a (a >= 9); phase 4/(5 pi a^2) <= (1/100)/a
      resp. (3/100)/a; 2 (7/100) + 1/100 = 3/20 and 2 (9/100) + 3/100 = 21/100; (2 pi)^(3/4) <= 4.

    The numeric lemmas bound a|rsE1| by 0.0689 (a >= 26) and 0.0821 (a >= 9).  Untrusted design
    numerics (closed forms 0.0688 and 0.0770): ~/rh-team/rsc0/out/phase2/lean_numerics.py.

    Not yet `lean_lib`s (lakefile.toml untouched): compile with `lake env lean`; a landing PR adds
    append-only `[[lean_lib]]` entries for RS_B3Sharp and RS_BridgeSharp (and RS_AxiomGuardSharp).

    conjecture1_proved = False.  An explicit finite-height remainder inequality; nothing here bears on
    the Riemann Hypothesis.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

section
namespace RSInt
end RSInt
open RSInt

/-! ## 1. Absolute Gaussian moments -/





































/-! ## 2. The saddle exponent split into its exact linear-plus-cubic part and a remainder -/











/-! ## 3. The near-zone majorant (|v| <= a/3, every a >= a0 >= 9) -/




































theorem solution {a0 a p v : ℝ} (h9 : 9 ≤ a0) (ha : a0 ≤ a) (hv : |v| ≤ a / 3) :
    ‖cexp (2 * ↑π * I * ((v : ℂ) * (1 + I)) ^ 2) / rsD (p + (v : ℂ) * (1 + I)) *
        (rsPhi a ((v : ℂ) * (1 + I)) - 1) * (1 + I)‖ ≤
      1 / (2 * π * a) *
          ((∑ j ∈ Finset.range 5, cMain j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2)) +
        Real.sqrt 2 / (2 * π * a ^ 2) *
          ((∑ j ∈ Finset.range 4, cEtwo j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2)) +
        Real.sqrt 2 * Real.exp (1 / (2 * a0 ^ 2)) / (2 * π * a ^ 2) *
          ((∑ j ∈ Finset.range 8, cS a0 j * |v| ^ j) * Real.exp (-(4 * π - 37 / 10) * v ^ 2)) := by
  have ha0 : 0 < a := by linarith
  rw [sum_cMain, sum_cEtwo, sum_cS]
  have hq0 := qMain_nonneg |v|
  have h1 : 0 ≤ 1 / (2 * π * a) * ((41 / 40 - 10 * π / 3 * |v| ^ 2 + 40 * π ^ 2 / 9 * |v| ^ 4) *
      Real.exp (-(4 * π) * v ^ 2)) :=
    mul_nonneg (by positivity) (mul_nonneg hq0 (Real.exp_pos _).le)
  have h2 : 0 ≤ Real.sqrt 2 / (2 * π * a ^ 2) *
      ((|v| + 4 * π * |v| ^ 3) * Real.exp (-(4 * π) * v ^ 2)) := by positivity
  have h3 : 0 ≤ Real.sqrt 2 * Real.exp (1 / (2 * a0 ^ 2)) / (2 * π * a ^ 2) *
      (|v| * (Real.sqrt 2 / 2 * (1 + 8 * π / 3 * |v| ^ 2) + (|v| + 4 * π * |v| ^ 3) / a0) ^ 2 *
        Real.exp (-(4 * π - 37 / 10) * v ^ 2)) := by positivity
  rcases eq_or_ne v 0 with rfl | hv0
  · have h0 : rsPhi a (((0 : ℝ) : ℂ) * (1 + I)) = 1 := by simp [rsPhi]
    rw [h0, sub_self, mul_zero, zero_mul, norm_zero]
    linarith
  have hvpos : 0 < |v| := abs_pos.mpr hv0
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnv : ‖(v : ℂ) * (1 + I)‖ = Real.sqrt 2 * |v| := norm_w_eq v
  have hn2 : ‖(v : ℂ) * (1 + I)‖ ^ 2 = 2 * v ^ 2 := by rw [hnv, mul_pow, hs2, sq_abs]
  have hn4 : ‖(v : ℂ) * (1 + I)‖ ^ 4 = 4 * v ^ 4 := by
    have : ‖(v : ℂ) * (1 + I)‖ ^ 4 = (‖(v : ℂ) * (1 + I)‖ ^ 2) ^ 2 := by ring
    rw [this, hn2]; ring
  have hna : ‖(v : ℂ) * (1 + I)‖ ≤ a / 2 := by
    rw [hnv]
    calc Real.sqrt 2 * |v| ≤ 3 / 2 * (a / 3) :=
          mul_le_mul sqrt_two_le_three_halves hv (abs_nonneg _) (by norm_num)
      _ = a / 2 := by ring
  have hphi := _root_.RSInt.norm_rsPhi_sub_one_le_prime ha0 hna
  rw [rsEone_line ha0 v, hn2, hn4] at hphi
  have hη1 := near_eta_le_lin (v := v) h9 ha
  have hη2 := near_eta_le_sq h9 ha hv
  have hη0 : 0 ≤ Real.sqrt 2 / 2 * |v| * |1 - 8 * π * v ^ 2 / 3| / a +
      (π * (4 * v ^ 4) / a ^ 2 + 2 * v ^ 2 / (2 * a ^ 2)) := by positivity
  have hexpη : Real.exp (Real.sqrt 2 / 2 * |v| * |1 - 8 * π * v ^ 2 / 3| / a +
      (π * (4 * v ^ 4) / a ^ 2 + 2 * v ^ 2 / (2 * a ^ 2))) ≤
      Real.exp (1 / (2 * a0 ^ 2)) * Real.exp (37 / 10 * v ^ 2) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hG0 : 0 < Real.exp (-(4 * π) * v ^ 2) := Real.exp_pos _
  have hGe : Real.exp (-(4 * π) * v ^ 2) * Real.exp (37 / 10 * v ^ 2) =
      Real.exp (-(4 * π - 37 / 10) * v ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hexpw : ‖cexp (2 * ↑π * I * ((v : ℂ) * (1 + I)) ^ 2)‖ = Real.exp (-(4 * π) * v ^ 2) :=
    norm_exp_gauss_diag v
  have him : ((p : ℂ) + (v : ℂ) * (1 + I)).im = v := by simp
  have hD : 2 * π * |v| ≤ ‖rsD (p + (v : ℂ) * (1 + I))‖ := by
    have := norm_rsD_ge_two_pi_im (p + (v : ℂ) * (1 + I)); rwa [him] at this
  have hT1 := near_T1 (G := Real.exp (-(4 * π) * v ^ 2)) ha0 hvpos hG0.le
    (abs_one_sub_le_quad (8 * π * v ^ 2 / 3))
  have hQ' : 41 / 40 - 5 / 4 * (8 * π * v ^ 2 / 3) + 5 / 8 * (8 * π * v ^ 2 / 3) ^ 2 =
      41 / 40 - 10 * π / 3 * |v| ^ 2 + 40 * π ^ 2 / 9 * |v| ^ 4 := by
    have h4abs : |v| ^ 4 = v ^ 4 := by
      rw [show |v| ^ 4 = (|v| ^ 2) ^ 2 by ring, sq_abs]; ring
    rw [sq_abs, h4abs]; ring
  rw [hQ'] at hT1
  have hT2 := near_T2 (G := Real.exp (-(4 * π) * v ^ 2)) ha0 hv0
  have hT3 := near_T3 (a0 := a0) ha0 hvpos hG0.le hη0 hη1 hexpη hGe
  calc ‖cexp (2 * ↑π * I * ((v : ℂ) * (1 + I)) ^ 2) / rsD (p + (v : ℂ) * (1 + I)) *
        (rsPhi a ((v : ℂ) * (1 + I)) - 1) * (1 + I)‖
      = Real.exp (-(4 * π) * v ^ 2) * ‖rsPhi a ((v : ℂ) * (1 + I)) - 1‖ * Real.sqrt 2 /
          ‖rsD (p + (v : ℂ) * (1 + I))‖ := by
        rw [norm_mul, norm_mul, norm_div, hexpw, norm_one_add_I]; ring
    _ ≤ Real.exp (-(4 * π) * v ^ 2) * ((Real.sqrt 2 / 2 * |v| * |1 - 8 * π * v ^ 2 / 3| / a +
          (π * (4 * v ^ 4) / a ^ 2 + 2 * v ^ 2 / (2 * a ^ 2))) +
          (Real.sqrt 2 / 2 * |v| * |1 - 8 * π * v ^ 2 / 3| / a +
            (π * (4 * v ^ 4) / a ^ 2 + 2 * v ^ 2 / (2 * a ^ 2))) ^ 2 *
          Real.exp (Real.sqrt 2 / 2 * |v| * |1 - 8 * π * v ^ 2 / 3| / a +
            (π * (4 * v ^ 4) / a ^ 2 + 2 * v ^ 2 / (2 * a ^ 2)))) * Real.sqrt 2 /
          (2 * π * |v|) := by
        gcongr
    _ = Real.exp (-(4 * π) * v ^ 2) * (Real.sqrt 2 / 2 * |v| * |1 - 8 * π * v ^ 2 / 3| / a) *
          Real.sqrt 2 / (2 * π * |v|) +
        Real.exp (-(4 * π) * v ^ 2) * (π * (4 * v ^ 4) / a ^ 2 + 2 * v ^ 2 / (2 * a ^ 2)) *
          Real.sqrt 2 / (2 * π * |v|) +
        Real.exp (-(4 * π) * v ^ 2) *
          ((Real.sqrt 2 / 2 * |v| * |1 - 8 * π * v ^ 2 / 3| / a +
            (π * (4 * v ^ 4) / a ^ 2 + 2 * v ^ 2 / (2 * a ^ 2))) ^ 2 *
          Real.exp (Real.sqrt 2 / 2 * |v| * |1 - 8 * π * v ^ 2 / 3| / a +
            (π * (4 * v ^ 4) / a ^ 2 + 2 * v ^ 2 / (2 * a ^ 2)))) * Real.sqrt 2 /
          (2 * π * |v|) := by ring
    _ ≤ _ := by rw [hT2]; linarith

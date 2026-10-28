-- Prove2me | solution 1 for RSInt.norm_rsPhi_sub_one_le_prime
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:00:05.718141+00:00
-- url     : https://prove2.me/submissions/2c9566c3-ed54-4657-a311-4b721b84a553

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

theorem logTaylor_three (u : ℂ) : logTaylor 3 u = u - u ^ 2 / 2 := by
  simp [logTaylor, Finset.sum_range_succ]
  ring

theorem rsPhi_eq_exp {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : 1 + w / a ≠ 0) :
    rsPhi a w = cexp (-(2 * ↑π * a ^ 2 * I) * (Complex.log (1 + w / a) - logTaylor 3 (w / a)) -
      1 / 2 * Complex.log (1 + w / a)) := by
  unfold rsPhi
  rw [Complex.cpow_def_of_ne_zero hw, ← Complex.exp_add, logTaylor_three]
  congr 1
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  field_simp
  ring



/-! ## 4. The saddle point is a global maximum along the steepest-descent line -/









/-! ## 4b. Integrability of the second Gaussian moment -/



/-! ## 5. The tau = 2 Mordell integral is uniformly bounded -/











/-! ## 6. The error integral `rsE1` is `O(1/a)` -/

















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



theorem logTaylor_two (u : ℂ) : logTaylor 2 u = u := by
  simp [logTaylor, Finset.sum_range_succ]

theorem logTaylor_four (u : ℂ) : logTaylor 4 u = u - u ^ 2 / 2 + u ^ 3 / 3 := by
  simp [logTaylor, Finset.sum_range_succ]
  ring





/-! ## 3. The near-zone majorant (|v| <= a/3, every a >= a0 >= 9) -/





































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








theorem solution {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : ‖w‖ ≤ a / 2) :
    ‖rsPhi a w - 1‖ ≤ ‖rsEone a w‖ + (π * ‖w‖ ^ 4 / a ^ 2 + ‖w‖ ^ 2 / (2 * a ^ 2)) +
      (‖rsEone a w‖ + (π * ‖w‖ ^ 4 / a ^ 2 + ‖w‖ ^ 2 / (2 * a ^ 2))) ^ 2 *
        Real.exp (‖rsEone a w‖ + (π * ‖w‖ ^ 4 / a ^ 2 + ‖w‖ ^ 2 / (2 * a ^ 2))) := by
  set u : ℂ := w / a with hu
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have hnu : ‖u‖ = ‖w‖ / a := by
    rw [hu, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have hu2 : ‖u‖ ≤ 1 / 2 := by rw [hnu, div_le_iff₀ ha]; linarith
  have hu1 : ‖u‖ < 1 := by linarith
  have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have h1u : 1 + u ≠ 0 := by
    intro h
    have : u = -1 := by linear_combination h
    rw [this, norm_neg, norm_one] at hu1; linarith
  set B : ℝ := π * ‖w‖ ^ 4 / a ^ 2 + ‖w‖ ^ 2 / (2 * a ^ 2) with hB
  set E : ℂ := -(2 * ↑π * a ^ 2 * I) * (Complex.log (1 + u) - logTaylor 3 u) -
    1 / 2 * Complex.log (1 + u) with hE
  set E2 : ℂ := -(2 * ↑π * a ^ 2 * I) * (Complex.log (1 + u) - logTaylor 4 u) -
    1 / 2 * (Complex.log (1 + u) - logTaylor 2 u) with hE2
  have hsplit : E = rsEone a w + E2 := by
    have hw' : w = u * a := by rw [hu]; field_simp
    rw [hE, hE2, rsEone, logTaylor_four, logTaylor_three, logTaylor_two, hw']
    field_simp
    ring
  have hn : ‖(2 * ↑π * a ^ 2 * I : ℂ)‖ = 2 * π * a ^ 2 := by
    rw [norm_mul, Complex.norm_I, mul_one,
      show (2 * (π : ℂ) * (a : ℂ) ^ 2 : ℂ) = ((2 * π * a ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hE2b : ‖E2‖ ≤ B := by
    have hT4 := Complex.norm_log_sub_logTaylor_le 3 hu1
    have hT2 := Complex.norm_log_sub_logTaylor_le 1 hu1
    have hnu0 : 0 ≤ ‖u‖ := norm_nonneg _
    have e1 : ‖-(2 * ↑π * a ^ 2 * I) * (Complex.log (1 + u) - logTaylor 4 u)‖ ≤
        2 * π * a ^ 2 * (‖u‖ ^ 4 / 2) := by
      rw [norm_mul, norm_neg, hn]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc ‖Complex.log (1 + u) - logTaylor 4 u‖ ≤ ‖u‖ ^ (3 + 1) * (1 - ‖u‖)⁻¹ / (3 + 1) := by
            exact_mod_cast hT4
        _ ≤ ‖u‖ ^ 4 / 2 := by
            have : ‖u‖ ^ (3 + 1) * (1 - ‖u‖)⁻¹ ≤ ‖u‖ ^ 4 * 2 :=
              mul_le_mul_of_nonneg_left hinv (by positivity)
            norm_num at this ⊢
            linarith
    have e2 : ‖(1 / 2 : ℂ) * (Complex.log (1 + u) - logTaylor 2 u)‖ ≤ 1 / 2 * ‖u‖ ^ 2 := by
      rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc ‖Complex.log (1 + u) - logTaylor 2 u‖ ≤ ‖u‖ ^ (1 + 1) * (1 - ‖u‖)⁻¹ / (1 + 1) := by
            exact_mod_cast hT2
        _ ≤ ‖u‖ ^ 2 := by
            have : ‖u‖ ^ (1 + 1) * (1 - ‖u‖)⁻¹ ≤ ‖u‖ ^ 2 * 2 :=
              mul_le_mul_of_nonneg_left hinv (by positivity)
            norm_num at this ⊢
            linarith
    calc ‖E2‖ ≤ ‖-(2 * ↑π * a ^ 2 * I) * (Complex.log (1 + u) - logTaylor 4 u)‖ +
          ‖(1 / 2 : ℂ) * (Complex.log (1 + u) - logTaylor 2 u)‖ := norm_sub_le _ _
      _ ≤ 2 * π * a ^ 2 * (‖u‖ ^ 4 / 2) + 1 / 2 * ‖u‖ ^ 2 := add_le_add e1 e2
      _ = B := by rw [hB, hnu]; field_simp
  have hEb : ‖E‖ ≤ ‖rsEone a w‖ + B := by
    rw [hsplit]; exact (norm_add_le _ _).trans (by linarith)
  have hB0 : 0 ≤ B := by positivity
  rw [rsPhi_eq_exp ha h1u, ← hE]
  have hexp := Complex.norm_exp_sub_sum_le_norm_mul_exp E 2
  have hsum : ∑ m ∈ Finset.range 2, E ^ m / (m.factorial : ℂ) = 1 + E := by
    simp [Finset.sum_range_succ]
  rw [hsum] at hexp
  have hR : ‖cexp E - (1 + E)‖ ≤ (‖rsEone a w‖ + B) ^ 2 * Real.exp (‖rsEone a w‖ + B) :=
    hexp.trans (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hEb 2) (Real.exp_le_exp.mpr hEb)
      (Real.exp_pos _).le (by positivity))
  have e : cexp E - 1 = E + (cexp E - (1 + E)) := by ring
  rw [e]
  calc ‖E + (cexp E - (1 + E))‖ ≤ ‖E‖ + ‖cexp E - (1 + E)‖ := norm_add_le _ _
    _ ≤ (‖rsEone a w‖ + B) + (‖rsEone a w‖ + B) ^ 2 * Real.exp (‖rsEone a w‖ + B) :=
        add_le_add hEb hR

-- Prove2me | solution 1 for RSSeam.E1_const_le
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:10:36.892797+00:00
-- url     : https://prove2.me/submissions/fe1b8160-eba2-4350-ac66-c1bd022a29a9

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
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







/-! ## 4. The saddle point is a global maximum along the steepest-descent line -/









/-! ## 4b. Integrability of the second Gaussian moment -/



/-! ## 5. The tau = 2 Mordell integral is uniformly bounded -/











/-! ## 6. The error integral `rsE1` is `O(1/a)` -/



theorem sqrt_two_le_three_halves : Real.sqrt 2 ≤ 3 / 2 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]













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








theorem solution {a : ℝ} (ha : 9 ≤ a) :
    Real.exp (1 / 600) / (π * a) * (13 / 25) * Real.sqrt (π / 7) +
      Real.exp (1 / 600) / (π * a) * (17 / 2) * (Real.sqrt (π / 7) / (2 * 7)) +
      5 * Real.exp (-(π * a ^ 2 / 18)) * Real.sqrt (π / (π / 2)) ≤ 1 / 4 / a := by
  have ha0 : 0 < a := by linarith
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d4
  have he : Real.exp (1 / 600) ≤ 600 / 599 := by
    have := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 600) (by norm_num) (by norm_num)
    have e : (1 : ℝ) / (1 - 1 / 600) = 600 / 599 := by norm_num
    linarith
  have hs : Real.sqrt (π / 7) ≤ 67 / 100 := by
    calc Real.sqrt (π / 7) ≤ Real.sqrt ((67 / 100) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 67 / 100 := Real.sqrt_sq (by norm_num)
  have hs0 : 0 ≤ Real.sqrt (π / 7) := Real.sqrt_nonneg _
  have hT12 : Real.exp (1 / 600) / (π * a) * (13 / 25) * Real.sqrt (π / 7) +
      Real.exp (1 / 600) / (π * a) * (17 / 2) * (Real.sqrt (π / 7) / (2 * 7)) ≤
      49 / 200 / a := by
    have e : Real.exp (1 / 600) / (π * a) * (13 / 25) * Real.sqrt (π / 7) +
        Real.exp (1 / 600) / (π * a) * (17 / 2) * (Real.sqrt (π / 7) / (2 * 7)) =
        (Real.exp (1 / 600) * Real.sqrt (π / 7) * (789 / 700) / π) / a := by
      field_simp; ring
    rw [e]
    apply div_le_div_of_nonneg_right _ ha0.le
    rw [div_le_iff₀ Real.pi_pos]
    have := mul_le_mul he hs hs0 (by norm_num)
    nlinarith
  have hT3 : 5 * Real.exp (-(π * a ^ 2 / 18)) * Real.sqrt (π / (π / 2)) ≤ 1 / 200 / a := by
    set x := π * a ^ 2 / 18 with hx
    have ha2 : 81 ≤ a ^ 2 := by nlinarith
    have hx14 : 14 ≤ x := by
      rw [hx, le_div_iff₀ (by norm_num)]
      nlinarith [mul_le_mul_of_nonneg_right hpi1.le (sq_nonneg a)]
    have hax : a ≤ x := by
      have h28 : 28 ≤ π * a := by nlinarith
      rw [hx]
      nlinarith
    have hexp : Real.exp (-x) ≤ 40320 / x ^ 8 := by
      rw [Real.exp_neg]
      have h8 := Real.pow_div_factorial_le_exp x (by linarith) 8
      have hpos : 0 < x ^ 8 / (Nat.factorial 8) := by positivity
      calc (Real.exp x)⁻¹ ≤ (x ^ 8 / (Nat.factorial 8))⁻¹ := inv_anti₀ hpos h8
        _ = 40320 / x ^ 8 := by norm_num [Nat.factorial]
    have hs2 : Real.sqrt (π / (π / 2)) = Real.sqrt 2 := by
      congr 1; field_simp
    rw [hs2, le_div_iff₀ ha0]
    have hx0 : 0 < x := by linarith
    calc 5 * Real.exp (-x) * Real.sqrt 2 * a ≤ 5 * (40320 / x ^ 8) * (3 / 2) * x := by
          gcongr
          exact sqrt_two_le_three_halves
      _ = 302400 / x ^ 7 := by field_simp; ring
      _ ≤ 1 / 200 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          have : (14 : ℝ) ^ 7 ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) hx14 7
          nlinarith
  calc _ ≤ 49 / 200 / a + 1 / 200 / a := add_le_add hT12 hT3
    _ = 1 / 4 / a := by ring

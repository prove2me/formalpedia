-- Prove2me | solution 1 for RSInt.rs_remainder_C0_alpha_prime
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:33:31.22002+00:00
-- url     : https://prove2.me/submissions/2ebaaa86-c6d2-480c-b686-91ffa59d4877

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
import Theorems.Thm_RSInt_E1_sharp_const_main
import Theorems.Thm_RSInt_norm_rsE1_le_prime
import Theorems.Thm_RSInt_norm_rsJ_le_prime
import Theorems.Thm_RSInt_rs_remainder_exact
namespace RSInt
end RSInt
/-  RS_B3.lean -- lane RS, brick B3 (the explicit Riemann-Siegel remainder), part 2: the exact
    saddle-point reduction.  Mathlib-only (imports `RS_C0`).

    ## Vocabulary (height t > 0)

        a = rsAlpha t = sqrt(t / 2 pi),  N = rsNn t = floor a,  p = rsFrac t = a - N,
        rsThetaMain t = (t/2) log t - (t/2) log(2 pi) - t/2 - pi/8   (verbatim the corpus thetaMain),
        rsPsi p = cos(2 pi (p^2 - p - 1/16)) / cos(2 pi p)            (Gabcke's C0 = Riemann's Psi),
        rsRem t = -lineUp (N + 1/2) (x |-> rsG x x^(-(1/2 + i t)))    (the exact RS remainder, B2).

    By B2 (`completed_re_eq_rs_cos`), on the critical line
        Re completedRiemannZeta(1/2+it) = 2M ( sum_{n<=N} n^(-1/2) cos(phi - t log n) + Re(e^{i phi} rsRem t) ).

    ## What this file proves (no `sorry`, no `native_decide`, no new axioms)

      * `rsRem_factor` : moving the remainder line to the saddle point a and factoring out the
        stationary phase,
            rsRem t = (-1)^(N+1) e^{i pi a^2} a^(-s) (rsJ p + rsE1 a p),
        where rsJ is the tau = 2 Mordell integral (RS_C0) and rsE1 the error integral of the amplitude
        rsPhi a w - 1,  rsPhi a w = e^{2 pi i a w - pi i w^2} (1 + w/a)^(-s).
      * `rs_phase` : e^{i phi} e^{i pi a^2} a^(-s) = a^(-1/2) e^{i (phi - rsThetaMain t - pi/8)}.
      * `rs_remainder_exact` : the EXACT identity
            2 Re(e^{i phi} rsRem t) - (-1)^(N+1) a^(-1/2) Psi(p)
              = (-1)^(N+1) a^(-1/2) [ 2 Re(e^{-i pi/8}(e^{i delta} - 1) rsJ p)
                                      + 2 Re(e^{i (delta - pi/8)} rsE1 a p) ],   delta = phi - thetaMain t,
        so the C0-corrected remainder is controlled by |delta| |rsJ p| and |rsE1 a p| alone.

    conjecture1_proved = False.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

namespace RSInt

/-! ## 0. Vocabulary -/



















theorem rsAlpha_sq {t : ℝ} (ht : 0 ≤ t) : rsAlpha t ^ 2 = t / (2 * π) :=
  Real.sq_sqrt (by positivity)

theorem t_eq_rsAlpha {t : ℝ} (ht : 0 ≤ t) : t = 2 * π * rsAlpha t ^ 2 := by
  rw [rsAlpha_sq ht]; field_simp



theorem rsAlpha_lt {t : ℝ} : rsAlpha t < rsNn t + 1 := Nat.lt_floor_add_one _

theorem rsFrac_lt_one {t : ℝ} : rsFrac t < 1 := by
  unfold rsFrac; linarith [rsAlpha_lt (t := t)]



/-! ## 1. Shifting the denominator by an integer -/



/-! ## 2. The factorization at the saddle point -/











/-! ## 3. The phase -/



/-! ## 4. The exact C0-corrected remainder -/



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





































/-! ## 4. The error integral, sharpened -/











/-! ## 5. Numerics -/

























theorem norm_rsE1_le_main {a p : ℝ} (ha : 26 ≤ a) : ‖rsE1 a p‖ ≤ 7 / 100 / a :=
  (_root_.RSInt.norm_rsE1_le_prime (p := p) (a0 := 26) (by norm_num) ha).trans (E1_sharp_const_main ha)



/-! ## 6. The tau = 2 Mordell integral: `|rsJ p| <= 4/5` (completing the square on the midline) -/





/-! ## 7. The sharpened C0 remainder bound, `a >= 26` (t >= 4250) -/

theorem rsAlpha_ge_26 {t : ℝ} (ht : 4250 ≤ t) : 26 ≤ rsAlpha t := by
  unfold rsAlpha
  rw [Real.le_sqrt (by norm_num) (by positivity), le_div_iff₀ (by positivity)]
  nlinarith [Real.pi_lt_d4]





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





































/-! ## 4. The error integral, sharpened -/











/-! ## 5. Numerics -/





























/-! ## 6. The tau = 2 Mordell integral: `|rsJ p| <= 4/5` (completing the square on the midline) -/





/-! ## 7. The sharpened C0 remainder bound, `a >= 26` (t >= 4250) -/




theorem solution {t : ℝ} (ht : 4250 ≤ t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) {φ : ℝ} (hφ : |φ - rsThetaMain t| ≤ 1 / t) :
    |2 * (cexp (I * φ) * rsRem t).re -
        (-1 : ℝ) ^ (rsNn t + 1) * (rsAlpha t) ^ (-(1 / 2 : ℝ)) * rsPsi (rsFrac t)| ≤
      3 / 20 * (rsAlpha t) ^ (-(3 / 2 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  rw [rs_remainder_exact ht0 hp hcos φ]
  have ha26 : 26 ≤ rsAlpha t := rsAlpha_ge_26 ht
  have hta : t = 2 * π * rsAlpha t ^ 2 := t_eq_rsAlpha ht0.le
  set a := rsAlpha t with ha_def
  have ha0 : 0 < a := by linarith
  have hJ : ‖rsJ (rsFrac t)‖ ≤ 4 / 5 := _root_.RSInt.norm_rsJ_le_prime hp rsFrac_lt_one
  have hE : ‖rsE1 a (rsFrac t)‖ ≤ 7 / 100 / a := norm_rsE1_le_main ha26
  have hA : |2 * (cexp (-(↑π / 8 * I)) * (cexp (I * (φ - rsThetaMain t)) - 1) *
      rsJ (rsFrac t)).re| ≤ 2 * (|φ - rsThetaMain t| * (4 / 5)) := by
    rw [abs_mul, abs_two]
    gcongr
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖cexp (-(↑π / 8 * I))‖ = 1 := by rw [Complex.norm_exp]; simp
    have h2 : ‖cexp (I * (φ - rsThetaMain t)) - 1‖ ≤ |φ - rsThetaMain t| := by
      have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := φ - rsThetaMain t)
      push_cast at this; rwa [Real.norm_eq_abs] at this
    rw [h1, one_mul]
    exact mul_le_mul h2 hJ (norm_nonneg _) (abs_nonneg _)
  have hB : |2 * (cexp (I * (φ - rsThetaMain t - π / 8)) * rsE1 a (rsFrac t)).re| ≤
      2 * (7 / 100 / a) := by
    rw [abs_mul, abs_two]
    gcongr
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul]
    have h1 : ‖cexp (I * (φ - rsThetaMain t - π / 8))‖ = 1 := by rw [Complex.norm_exp]; simp
    rw [h1, one_mul]; exact hE
  have hδ : |φ - rsThetaMain t| ≤ 1 / (2 * π * a ^ 2) := by rw [← hta]; exact hφ
  have h8 : 8 / 5 * |φ - rsThetaMain t| ≤ 1 / 100 / a := by
    have h1 : 8 / 5 * |φ - rsThetaMain t| ≤ 8 / 5 * (1 / (2 * π * a ^ 2)) := by linarith
    refine h1.trans ?_
    rw [show 8 / 5 * (1 / (2 * π * a ^ 2)) = 4 / (5 * π * a ^ 2) by field_simp; ring,
      div_le_div_iff₀ (by positivity) ha0]
    have : 80 ≤ π * a := by nlinarith [Real.pi_gt_d2]
    nlinarith
  rw [abs_mul, abs_mul]
  have hsign : |(-1 : ℝ) ^ (rsNn t + 1)| = 1 := by simp
  rw [hsign, one_mul, abs_of_pos (Real.rpow_pos_of_pos ha0 _)]
  have hapos := Real.rpow_pos_of_pos ha0 (-(1 / 2 : ℝ))
  calc a ^ (-(1 / 2 : ℝ)) * |2 * (cexp (-(↑π / 8 * I)) * (cexp (I * (φ - rsThetaMain t)) - 1) *
        rsJ (rsFrac t)).re + 2 * (cexp (I * (φ - rsThetaMain t - π / 8)) *
        rsE1 a (rsFrac t)).re|
      ≤ a ^ (-(1 / 2 : ℝ)) * (2 * (|φ - rsThetaMain t| * (4 / 5)) + 2 * (7 / 100 / a)) := by
        gcongr
        exact (abs_add_le _ _).trans (add_le_add hA hB)
    _ ≤ a ^ (-(1 / 2 : ℝ)) * (3 / 20 / a) := by
        gcongr
        have e : (3 : ℝ) / 20 / a = 1 / 100 / a + 2 * (7 / 100 / a) := by ring
        rw [e]; linarith
    _ = 3 / 20 * a ^ (-(3 / 2 : ℝ)) := by
        rw [show (-(3 / 2 : ℝ)) = -(1 / 2) + -1 by norm_num, Real.rpow_add ha0, Real.rpow_neg_one]
        ring

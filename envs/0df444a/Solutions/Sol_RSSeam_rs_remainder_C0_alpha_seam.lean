-- Prove2me | solution 1 for RSSeam.rs_remainder_C0_alpha_seam
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:34:18.401017+00:00
-- url     : https://prove2.me/submissions/d9d964b2-6cf6-4834-8921-ec2ca19010b2

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_norm_rsJ_le
import Theorems.Thm_RSInt_rs_remainder_exact
import Theorems.Thm_RSSeam_E1_const_le
import Theorems.Thm_RSSeam_norm_rsE1_le
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

namespace RSSeam

open RSInt









/-! ## The explicit C0 remainder bound from t >= 509 -/

theorem rsAlpha_ge_9 {t : ℝ} (ht : 509 ≤ t) : 9 ≤ rsAlpha t := by
  unfold rsAlpha
  rw [Real.le_sqrt (by norm_num) (by positivity), le_div_iff₀ (by positivity)]
  nlinarith [Real.pi_lt_d4]





end RSSeam

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









/-! ## The explicit C0 remainder bound from t >= 509 -/




theorem solution {t : ℝ} (ht : 509 ≤ t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) {φ : ℝ} (hφ : |φ - rsThetaMain t| ≤ 1 / t) :
    |2 * (cexp (I * φ) * rsRem t).re -
        (-1 : ℝ) ^ (rsNn t + 1) * (rsAlpha t) ^ (-(1 / 2 : ℝ)) * rsPsi (rsFrac t)| ≤
      13 / 20 * (rsAlpha t) ^ (-(3 / 2 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  rw [rs_remainder_exact ht0 hp hcos φ]
  have ha9 : 9 ≤ rsAlpha t := rsAlpha_ge_9 ht
  have hta : t = 2 * π * rsAlpha t ^ 2 := t_eq_rsAlpha ht0.le
  set a := rsAlpha t with ha_def
  have ha0 : 0 < a := by linarith
  have hJ : ‖rsJ (rsFrac t)‖ ≤ 4 := norm_rsJ_le hp rsFrac_lt_one
  have hE : ‖rsE1 a (rsFrac t)‖ ≤ 1 / 4 / a := (norm_rsE1_le ha9).trans (E1_const_le ha9)
  have hA : |2 * (cexp (-(↑π / 8 * I)) * (cexp (I * (φ - rsThetaMain t)) - 1) *
      rsJ (rsFrac t)).re| ≤ 2 * (|φ - rsThetaMain t| * 4) := by
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
      2 * (1 / 4 / a) := by
    rw [abs_mul, abs_two]
    gcongr
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul]
    have h1 : ‖cexp (I * (φ - rsThetaMain t - π / 8))‖ = 1 := by rw [Complex.norm_exp]; simp
    rw [h1, one_mul]; exact hE
  have hδ : |φ - rsThetaMain t| ≤ 1 / (2 * π * a ^ 2) := by rw [← hta]; exact hφ
  have h8 : 8 * |φ - rsThetaMain t| ≤ 3 / 20 / a := by
    have h1 : 8 * |φ - rsThetaMain t| ≤ 8 * (1 / (2 * π * a ^ 2)) := by linarith
    refine h1.trans ?_
    rw [show 8 * (1 / (2 * π * a ^ 2)) = 4 / (π * a ^ 2) by field_simp; ring,
      div_le_div_iff₀ (by positivity) ha0]
    have : 28 ≤ π * a := by nlinarith [Real.pi_gt_d2]
    nlinarith
  rw [abs_mul, abs_mul]
  have hsign : |(-1 : ℝ) ^ (rsNn t + 1)| = 1 := by simp
  rw [hsign, one_mul, abs_of_pos (Real.rpow_pos_of_pos ha0 _)]
  have hapos := Real.rpow_pos_of_pos ha0 (-(1 / 2 : ℝ))
  calc a ^ (-(1 / 2 : ℝ)) * |2 * (cexp (-(↑π / 8 * I)) * (cexp (I * (φ - rsThetaMain t)) - 1) *
        rsJ (rsFrac t)).re + 2 * (cexp (I * (φ - rsThetaMain t - π / 8)) *
        rsE1 a (rsFrac t)).re|
      ≤ a ^ (-(1 / 2 : ℝ)) * (2 * (|φ - rsThetaMain t| * 4) + 2 * (1 / 4 / a)) := by
        gcongr
        exact (abs_add_le _ _).trans (add_le_add hA hB)
    _ ≤ a ^ (-(1 / 2 : ℝ)) * (13 / 20 / a) := by
        gcongr
        have e : (13 : ℝ) / 20 / a = 3 / 20 / a + 2 * (1 / 4 / a) := by ring
        rw [e]; linarith
    _ = 13 / 20 * a ^ (-(3 / 2 : ℝ)) := by
        rw [show (-(3 / 2 : ℝ)) = -(1 / 2) + -1 by norm_num, Real.rpow_add ha0, Real.rpow_neg_one]
        ring

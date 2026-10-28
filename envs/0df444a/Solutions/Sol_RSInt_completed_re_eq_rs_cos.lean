-- Prove2me | solution 1 for RSInt.completed_re_eq_rs_cos
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:37:30.769907+00:00
-- url     : https://prove2.me/submissions/0b997dab-c49b-40f1-9b61-5396033da5a3

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_completedRiemannZeta_eq_rs

/-  RS_B2.lean -- lane RS, ANDURIL brick B2: RIEMANN'S INTEGRAL REPRESENTATION OF zeta(s) for
    general complex s, with the residue bookkeeping (the exact Riemann-Siegel formula).
    Mathlib-only (imports `RS_Entire`).

    ## The headline (`riemann_siegel_integral`)

    For every complex s that is not an odd positive integer (s ∉ {1, 3, 5, ...}), all N, M ∈ ℕ and
    every c1 ∈ (N, N+1), c2 ∈ (M, M+1):

      zeta(s) = sum_{n=1}^{N} n^(-s) + chi(s) sum_{m=1}^{M} m^(s-1)
                - lineUp c1 (x |-> rsG x x^(-s)) + chi(s) lineDn c2 (x |-> rsH x x^(s-1)),

      rsG x = e^{i pi x^2}/(e^{i pi x} - e^{-i pi x}),  rsH x = e^{-i pi x^2}/(e^{i pi x} - e^{-i pi x}),
      chi(s) = pi^(s-1/2) Gamma((1-s)/2) / Gamma(s/2),
      lineUp c F = int F(c + v(1+i))(1+i) dv,   lineDn c F = int F(c + v(1-i))(1-i) dv.

    This is Riemann's integral (Siegel 1932; Edwards ch. 7; Titchmarsh 2.10) in exactly the form
    used for the Riemann-Siegel saddle-point analysis: the remainder integrals run along the
    steepest-descent directions of e^{+-i pi x^2} and may cross the real axis anywhere in the gap.
    (At s = 3, 5, ... Mathlib's Gamma((1-s)/2) takes the junk value 0 at its pole, so those points
    are excluded; s = 1 is the pole of zeta.)

    ## How it is proved (no residue theorem, no Hankel contour)

      1. N = M = 0, Re s > 2 (`rs_identity_re_gt_two`): the Mellin identity (RS_Mellin: Fubini with
         the complex Gamma integral, the Mordell closed form, the Bose integral = Gamma zeta) and the
         folding of the chi-side line (RS_Fold), assembled with the Gamma identity for chi.
      2. All s ∉ {1,3,5,...} (`rs_identity`): identity theorem on the connected open set
         ℂ \ {1,3,5,...}; both sides are holomorphic there (RS_Entire).
      3. General N, M (`lineUp_book`, `lineDn_book`): induction, crossing one pole at a time
         (`lineUp_cross`, `lineDn_cross` in RS_Kernel).

    ## Critical line (`completedRiemannZeta_eq_rs`, `completed_re_eq_rs_cos`)

    For s = 1/2 + it and c ∈ (N, N+1), with S = sum_{n<=N} n^(-s) and R = -lineUp c (rsG x^(-s)):
        completedRiemannZeta s = 2 Re( Gammaℝ(s) (S + R) )        (a real number),
    and, whenever Gammaℝ(s) = M e^{i phi} with M > 0 (the island's polar form),
        Re completedRiemannZeta(s) = 2M ( sum_{n<=N} n^(-1/2) cos(phi - t log n) + Re(e^{i phi} R) ).
    So Z(t) = 2 sum n^(-1/2) cos(theta - t log n) + 2 Re(e^{i theta} R_N(t)) EXACTLY: the only
    analytic input left for sign certification is a bound on the remainder R_N(t) (brick B3).

    conjecture1_proved = False.  An exact integral identity for zeta; nothing here bears on RH.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

section
namespace RSInt
end RSInt
open RSInt

/-! ## 1. The identity for Re s > 2 -/





/-! ## 2. The domain ℂ \ {1, 3, 5, ...} -/









/-! ## 3. Riemann's integral for every s ∉ {1, 3, 5, ...} (N = M = 0) -/



/-! ## 4. Residue bookkeeping -/



















/-! ## 5. THE HEADLINE: Riemann's integral with the residue bookkeeping -/



/-! ## 6. The critical line -/














theorem solution (t : ℝ) (N : ℕ) {c : ℝ} (h : (N : ℝ) < c) (h' : c < N + 1)
    {M φ : ℝ} (hpolar : Gammaℝ ((1 / 2 : ℂ) + t * I) = (M : ℂ) * cexp (I * φ)) :
    (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re =
      2 * M * ((∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (φ - t * Real.log n)) +
        (cexp (I * φ) * -lineUp c (fun x => rsG x * x ^ (-((1 / 2 : ℂ) + t * I)))).re) := by
  rw [completedRiemannZeta_eq_rs t N h h', Complex.ofReal_re, hpolar]
  have hterm : ∀ n ∈ Finset.Icc 1 N, (cexp (I * φ) * (n : ℂ) ^ (-((1 / 2 : ℂ) + t * I))).re =
      (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (φ - t * Real.log n) := by
    intro n hn
    have hn1 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hpow : (n : ℂ) ^ (-((1 / 2 : ℂ) + t * I)) =
        (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (-(t * Real.log n) * I) := by
      rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; rfl,
        Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hn1.ne'), ← Complex.ofReal_log hn1.le,
        Complex.ofReal_cpow hn1.le, Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hn1.ne'),
        ← Complex.ofReal_log hn1.le, ← Complex.exp_add]
      congr 1; push_cast; ring
    rw [hpow, show cexp (I * φ) * ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        cexp (-(t * Real.log n) * I)) = (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        cexp (((φ - t * Real.log n : ℝ) : ℂ) * I) by
      rw [show (((φ - t * Real.log n : ℝ) : ℂ) * I) = I * φ + (-(t * Real.log n) * I) by
        push_cast; ring, Complex.exp_add]; ring]
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hsum : (cexp (I * φ) * ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-((1 / 2 : ℂ) + t * I))).re =
      ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (φ - t * Real.log n) := by
    rw [Finset.mul_sum, Complex.re_sum]
    exact Finset.sum_congr rfl hterm
  have hM : ((M : ℂ) * cexp (I * φ) * ((∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-((1 / 2 : ℂ) + t * I))) -
      lineUp c (fun x => rsG x * x ^ (-((1 / 2 : ℂ) + t * I))))).re =
      M * ((cexp (I * φ) * ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-((1 / 2 : ℂ) + t * I))).re +
        (cexp (I * φ) * -lineUp c (fun x => rsG x * x ^ (-((1 / 2 : ℂ) + t * I)))).re) := by
    rw [mul_assoc, Complex.re_ofReal_mul, mul_sub, sub_eq_add_neg, ← mul_neg, Complex.add_re]
  rw [hM, hsum]; ring

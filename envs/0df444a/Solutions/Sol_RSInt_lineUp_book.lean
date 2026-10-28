-- Prove2me | solution 1 for RSInt.lineUp_book
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:20:37.864203+00:00
-- url     : https://prove2.me/submissions/258e34d1-acb4-4971-bf35-5bf198b0d55e

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_lineUp_cpow_same_gap
import Theorems.Thm_RSInt_lineUp_cross
import Theorems.Thm_RSInt_norm_cpow_le_of_ge
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

namespace RSInt

/-! ## 1. The identity for Re s > 2 -/





/-! ## 2. The domain ℂ \ {1, 3, 5, ...} -/









/-! ## 3. Riemann's integral for every s ∉ {1, 3, 5, ...} (N = M = 0) -/



/-! ## 4. Residue bookkeeping -/



theorem slit_of_upStrip {x : ℂ} {a b : ℝ} (ha : 0 < a) (hx : x.re - x.im ∈ Icc a b) :
    x ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases h : x.im = 0
  · left; have := hx.1; rw [h] at this; linarith
  · right; exact h



theorem norm_ge_of_upStrip {x : ℂ} {a b : ℝ} (hx : x.re - x.im ∈ Icc a b) (_ha : 0 < a) :
    a / 2 ≤ ‖x‖ := by
  have h1 := Complex.abs_re_le_norm x
  have h2 := Complex.abs_im_le_norm x
  have := hx.1
  have h3 : x.re - x.im ≤ |x.re| + |x.im| := by
    linarith [le_abs_self x.re, neg_abs_le x.im]
  linarith











/-! ## 5. THE HEADLINE: Riemann's integral with the residue bookkeeping -/



/-! ## 6. The critical line -/















end RSInt

end

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
















theorem solution (s : ℂ) (N : ℕ) {c c₁ : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (h₁ : (N : ℝ) < c₁) (h₁' : c₁ < N + 1) :
    -lineUp c (fun x => rsG x * x ^ (-s)) =
      (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) - lineUp c₁ (fun x => rsG x * x ^ (-s)) := by
  induction N generalizing c₁ with
  | zero =>
    simp only [Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1), Finset.sum_empty, zero_sub]
    rw [lineUp_cpow_same_gap s (n := 0) (by simpa using hc) (by simpa using hc1)
      (by simpa using h₁) (by simpa using h₁')]
  | succ N ih =>
    have hN := ih (c₁ := (N : ℝ) + 1 / 2) (by linarith) (by linarith)
    have hc₁ : 0 < c₁ := lt_of_le_of_lt (by positivity) h₁
    have hcross := lineUp_cross (φ := fun x => x ^ (-s)) (n := (N : ℤ) + 1)
      (c₁ := (N : ℝ) + 1 / 2) (c₂ := c₁) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; push_cast at h₁; linarith) (by push_cast; push_cast at h₁'; linarith)
      (fun x hx => (differentiableAt_id).cpow (differentiableAt_const _)
        (slit_of_upStrip (by positivity) hx))
      (A := ((((N : ℝ) + 1 / 2) / 2) ^ (-s).re + 1) * Real.exp (π * |(-s).im|))
      (B := |(-s).re|) (fun x hx => norm_cpow_le_of_ge (by positivity)
        (norm_ge_of_upStrip hx (by positivity)))
    rw [hN, Finset.sum_Icc_succ_top (by omega), hcross]
    push_cast
    ring

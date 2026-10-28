-- Prove2me | solution 1 for RSInt.rsRem_factor
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:16:11.056727+00:00
-- url     : https://prove2.me/submissions/42db8bf1-15b9-4bf7-843c-d8c694c1188e

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_integrable_lineUp_rsG_mul
import Theorems.Thm_RSInt_integrable_of_continuous_of_tail
import Theorems.Thm_RSInt_lineUp_cpow_same_gap
import Theorems.Thm_RSInt_norm_cpow_le_of_ge
import Theorems.Thm_RSInt_rsG_cpow_factor
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









theorem rsD_eq_zero_iff (x : ℂ) : rsD x = 0 ↔ ∃ n : ℤ, x = n := by
  unfold rsD
  rw [sub_eq_zero, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : (2 * ↑π * I : ℂ) * x = (2 * ↑π * I) * n := by linear_combination hn
    exact mul_left_cancel₀ (by simp [I_ne_zero]) h2
  · rintro ⟨n, rfl⟩
    exact ⟨n, by ring⟩



theorem differentiable_rsD : Differentiable ℂ rsD := by
  unfold rsD; fun_prop













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

theorem one_le_norm_rsD {x : ℂ} (h : 1 ≤ |x.im|) : 1 ≤ ‖rsD x‖ := by
  have h1 := norm_rsD_ge x
  have hp : π ≤ π * |x.im| := by nlinarith [Real.pi_pos]
  have h2 : Real.exp π ≤ Real.exp (π * |x.im|) := Real.exp_le_exp.mpr hp
  have h3 : Real.exp (-(π * |x.im|)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, abs_nonneg x.im]
  have h4 : π + 1 ≤ Real.exp π := Real.add_one_le_exp π
  have h5 : 3 < π := Real.pi_gt_three
  linarith













/-! ## 3. The Fresnel line integral -/











/-! ## 4. Gaussian tails, line integrability, and the strip wrappers -/























/-! ## 5. Linearity and translation of line integrals -/

theorem lineUp_congr {F G : ℂ → ℂ} {c : ℝ}
    (h : ∀ v : ℝ, F (c + v * (1 + I)) = G (c + v * (1 + I))) : lineUp c F = lineUp c G := by
  unfold lineUp; congr 1; ext v; rw [h]



theorem lineUp_const_mul (k : ℂ) (F : ℂ → ℂ) (c : ℝ) :
    lineUp c (fun x => k * F x) = k * lineUp c F := by
  unfold lineUp; rw [← integral_const_mul]; congr 1; ext v; ring



theorem lineUp_sub_mul {F G : ℂ → ℂ} {c : ℝ} (k : ℂ)
    (hF : Integrable (fun v : ℝ => F (c + v * (1 + I))))
    (hG : Integrable (fun v : ℝ => G (c + v * (1 + I)))) :
    lineUp c (fun x => F x - k * G x) = lineUp c F - k * lineUp c G := by
  unfold lineUp
  rw [← integral_const_mul, ← integral_sub (hF.mul_const _) ((hG.mul_const _).const_mul _)]
  congr 1; ext v; ring



/-! ## 6. Holomorphy of the kernels off the integers -/

theorem rsD_ne_zero_of_ne {x : ℂ} (h : ∀ n : ℤ, x ≠ n) : rsD x ≠ 0 := by
  intro h0; obtain ⟨n, hn⟩ := (rsD_eq_zero_iff x).mp h0; exact h n hn





/-- A point of the slope-(+1) line through a non-integer `c` is never an integer. -/
theorem lineUp_pt_ne_int {c : ℝ} (hc : ∀ m : ℤ, (m : ℝ) ≠ c) (v : ℝ) (n : ℤ) :
    (c : ℂ) + v * (1 + I) ≠ n := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  rw [him] at hre
  exact hc n (by linarith)



theorem notInt_of_Ioo {c : ℝ} {n : ℤ} (h₁ : (n : ℝ) < c) (h₂ : c < n + 1) :
    ∀ m : ℤ, (m : ℝ) ≠ c := by
  intro m hm
  rw [← hm] at h₁ h₂
  have a : n < m := by exact_mod_cast h₁
  have b : m < n + 1 := by exact_mod_cast h₂
  omega

/-! ## 7. The Fresnel/Gaussian integrands are integrable along the lines -/









/-! ## 8. Moving the line inside a gap, and across a pole -/











/-! ## 9. The slope-(-1) side by conjugation -/

















/-! ## 10. The Mordell closed form -/



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

/-  RS_C0.lean -- lane RS, brick B3 (the Riemann-Siegel remainder), part 1: RIEMANN'S Psi.
    Mathlib-only (imports `RS_B2`).

    The main term of the Riemann-Siegel remainder is the Mordell integral with Gaussian e^{2 pi i w^2}
    (tau = 2):
        rsJ p = lineUp 0 (w |-> e^{2 pi i w^2} / (e^{i pi (p+w)} - e^{-i pi (p+w)})),   0 < p < 1.
    Its value is not elementary, but the combination that enters Z(t) is:

        2 Re(e^{-i pi/8} rsJ p) = cos(2 pi (p^2 - p - 1/16)) / cos(2 pi p) = Psi(p)   (Gabcke's C0).

    Proof (no residue theorem): write e^{i pi w^2} as a Gaussian Fourier integral along the (1-i)
    line, swap the two line integrals (Fubini), evaluate the inner one by the tau = 1 Mordell closed
    form (RS_Kernel), split the outer one into a tau = -1 Mordell integral (closed form by conjugation
    and one pole crossing) and a tau = -2 integral that is the conjugate of rsJ itself (symmetry
    rsJ(1-p) = rsJ(p)).  This gives rsJ + e^{i pi/4} conj(rsJ) = elementary, whose real part after the
    phase e^{-i pi/8} is Psi.

    conjecture1_proved = False.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

namespace RSInt

/-! ## 1. Linearity for `lineDn`, translations -/





theorem lineUp_shift (p : ℝ) (H : ℂ → ℂ) : lineUp 0 (fun w => H (p + w)) = lineUp p H := by
  unfold lineUp; congr 1; ext v; congr 2; push_cast; ring



/-! ## 2. The Gaussian as a Fourier integral along the (1-i) line -/





/-! ## 3. The tau = 2 Mordell integral and its symmetry -/







/-- A point `p + v (1+i)` with `0 < p < 1` is never an integer. -/
theorem pt_ne_int {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (v : ℝ) (n : ℤ) :
    (p : ℂ) + ((0 : ℝ) + v * (1 + I)) ≠ n := by
  have := lineUp_pt_ne_int (c := p) (notInt_of_Ioo (n := 0) (by simpa using hp)
    (by simpa using hp1)) v n
  simpa using this







/-! ## 4. Fubini: rsJ as an iterated integral -/



/-! ## 5. The inner integral: the tau = 1 Mordell closed form -/



/-! ## 6. The outer integral splits into T1 - T2 -/









/-! ## 7. T2 is the conjugate of rsJ; T1 by one pole crossing and the Mordell formula -/







/-! ## 8. Riemann's Psi -/



end RSInt

end

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

















theorem rsAlpha_pos {t : ℝ} (ht : 0 < t) : 0 < rsAlpha t := Real.sqrt_pos.mpr (by positivity)

theorem rsAlpha_sq {t : ℝ} (ht : 0 ≤ t) : rsAlpha t ^ 2 = t / (2 * π) :=
  Real.sq_sqrt (by positivity)

theorem t_eq_rsAlpha {t : ℝ} (ht : 0 ≤ t) : t = 2 * π * rsAlpha t ^ 2 := by
  rw [rsAlpha_sq ht]; field_simp



theorem rsAlpha_lt {t : ℝ} : rsAlpha t < rsNn t + 1 := Nat.lt_floor_add_one _

theorem rsFrac_lt_one {t : ℝ} : rsFrac t < 1 := by
  unfold rsFrac; linarith [rsAlpha_lt (t := t)]

theorem rsAlpha_eq {t : ℝ} : rsAlpha t = rsNn t + rsFrac t := by unfold rsFrac; ring

/-! ## 1. Shifting the denominator by an integer -/



/-! ## 2. The factorization at the saddle point -/

theorem upLine_ne_zero {a : ℝ} (ha : 0 < a) (v : ℝ) : (a : ℂ) + v * (1 + I) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  rw [him] at hre; linarith



theorem integrable_upLine_cpow {c : ℝ} (hc : 0 < c) (hcl : ∀ m : ℤ, (m : ℝ) ≠ c) (s : ℂ) :
    Integrable (fun v : ℝ => rsG ((c : ℂ) + v * (1 + I)) * ((c : ℂ) + v * (1 + I)) ^ (-s)) := by
  refine integrable_lineUp_rsG_mul (φ := fun x => x ^ (-s)) (c₁ := c) (c₂ := c) ⟨le_rfl, le_rfl⟩ hcl
    (fun x hx => continuousAt_cpow_const (slit_of_upStrip hc hx))
    (A := ((c / 2) ^ (-s).re + 1) * Real.exp (π * |(-s).im|)) (B := |(-s).re|)
    (fun x hx => norm_cpow_le_of_ge (by positivity) (norm_ge_of_upStrip hx hc))

theorem integrable_J2_integrand {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Integrable (fun v : ℝ => cexp (2 * ↑π * I * ((0 : ℝ) + v * (1 + I) : ℂ) ^ 2) /
      rsD (p + ((0 : ℝ) + v * (1 + I)))) := by
  refine integrable_of_continuous_of_tail ?_ (a := 4 * π) (b := 0) (C := 1) (R := 1)
    (by positivity) (fun v hv => ?_)
  · rw [continuous_iff_continuousAt]
    intro v
    have hD : rsD (p + ((0 : ℝ) + v * (1 + I))) ≠ 0 := rsD_ne_zero_of_ne (pt_ne_int hp hp1 v)
    exact ((by fun_prop : Continuous (fun v : ℝ =>
      cexp (2 * ↑π * I * ((0 : ℝ) + v * (1 + I) : ℂ) ^ 2))).continuousAt).div
      ((differentiable_rsD.continuous.comp (by fun_prop :
        Continuous (fun v : ℝ => (p : ℂ) + ((0 : ℝ) + v * (1 + I))))).continuousAt) hD
  · have h1 : 1 ≤ |((p : ℂ) + ((0 : ℝ) + v * (1 + I))).im| := by simpa using hv
    rw [norm_div, Complex.norm_exp]
    have hD := one_le_norm_rsD h1
    have hre : (2 * (π : ℂ) * I * ((0 : ℝ) + v * (1 + I) : ℂ) ^ 2).re =
        -(4 * π) * v ^ 2 + 0 * |v| := by
      simp [pow_two, mul_re, mul_im]; ring
    rw [hre, one_mul]
    exact div_le_self (Real.exp_pos _).le hD



/-! ## 3. The phase -/



/-! ## 4. The exact C0-corrected remainder -/



end RSInt

end

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

section
namespace RSInt
end RSInt
open RSInt

/-! ## 0. Vocabulary -/































/-! ## 1. Shifting the denominator by an integer -/



/-! ## 2. The factorization at the saddle point -/










theorem solution {t : ℝ} (ht : 0 < t) (hp : 0 < rsFrac t) :
    rsRem t = (-1) ^ (rsNn t + 1) * cexp (↑π * I * (rsAlpha t) ^ 2) *
      ((rsAlpha t : ℂ) ^ (-((1 / 2 : ℂ) + t * I))) *
        (rsJ (rsFrac t) + rsE1 (rsAlpha t) (rsFrac t)) := by
  set a := rsAlpha t with hadef
  set N := rsNn t with hNdef
  set p := rsFrac t with hpdef
  have ha : 0 < a := rsAlpha_pos ht
  have hN : a = N + p := rsAlpha_eq
  have hp1 : p < 1 := rsFrac_lt_one
  have hst : ((1 / 2 : ℂ) + t * I) = (1 / 2 : ℂ) + 2 * ↑π * a ^ 2 * I := by
    rw [t_eq_rsAlpha ht.le]; push_cast; ring
  set s : ℂ := (1 / 2 : ℂ) + 2 * ↑π * a ^ 2 * I with hs
  -- move the line to the saddle point
  have hmove : lineUp ((N : ℝ) + 1 / 2) (fun x => rsG x * x ^ (-((1 / 2 : ℂ) + t * I))) =
      lineUp a (fun x => rsG x * x ^ (-s)) := by
    rw [hst]
    exact lineUp_cpow_same_gap s (n := N) (by linarith) (by linarith) (by linarith)
      (by linarith [rsAlpha_lt (t := t)])
  have hcl : ∀ m : ℤ, (m : ℝ) ≠ a := notInt_of_Ioo (n := N) (by push_cast; linarith)
    (by push_cast; linarith [rsAlpha_lt (t := t)])
  set C : ℂ := (-1) ^ N * cexp (↑π * I * a ^ 2) * (a : ℂ) ^ (-s) with hC
  have hC0 : C ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (Complex.exp_ne_zero _)) ?_
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => (ofReal_ne_zero.mpr ha.ne') h.1
  set G : ℂ → ℂ := fun w => cexp (2 * ↑π * I * w ^ 2) / rsD (p + w) * rsPhi a w with hG
  have hpt : ∀ v : ℝ, rsG ((a : ℂ) + ((0 : ℝ) + v * (1 + I))) *
      ((a : ℂ) + ((0 : ℝ) + v * (1 + I))) ^ (-s) = C * G ((0 : ℝ) + v * (1 + I)) := by
    intro v
    have hw : (a : ℂ) + ((0 : ℝ) + v * (1 + I)) ≠ 0 := by
      have := upLine_ne_zero ha v; simpa using this
    rw [rsG_cpow_factor ha hN _ hw]
  have hshift : lineUp a (fun x => rsG x * x ^ (-s)) = C * lineUp 0 G := by
    rw [← lineUp_shift a, ← lineUp_const_mul]
    exact lineUp_congr fun v => hpt v
  -- integrability of G along the line through 0
  have hFint := integrable_upLine_cpow (c := a) ha hcl s
  have hGint : Integrable (fun v : ℝ => G ((0 : ℝ) + v * (1 + I))) := by
    have := hFint.const_mul C⁻¹
    refine this.congr (Eventually.of_forall fun v => ?_)
    have h := hpt v
    simp only at h ⊢
    rw [show ((a : ℂ) + ((0 : ℝ) + v * (1 + I))) = (a : ℂ) + v * (1 + I) by push_cast; ring] at h
    rw [h, ← mul_assoc, inv_mul_cancel₀ hC0, one_mul]
  have hJint := integrable_J2_integrand hp hp1
  have hE1 : rsE1 a p = lineUp 0 G - 1 * rsJ p := by
    unfold rsE1 rsJ
    rw [← lineUp_sub_mul 1 hGint hJint]
    refine lineUp_congr fun v => ?_
    simp only [hG]; ring
  unfold rsRem
  rw [hmove, hshift, hE1, hC, hst]
  ring

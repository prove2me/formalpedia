-- Prove2me | solution 1 for RSInt.rs_identity_re_gt_two
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:27:17.404327+00:00
-- url     : https://prove2.me/submissions/5a50f863-27b8-416f-879e-148e073bc520

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_integral_bose
import Theorems.Thm_RSInt_lineDn_zero_eq
import Theorems.Thm_RSInt_lineDn_zero_fold
import Theorems.Thm_RSInt_mellin_step
import Theorems.Thm_RSInt_rsChi_mul_Gamma_cos
import Theorems.Thm_RSInt_rsK_split
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







theorem pi_ne_zero' : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero



















/-! ## 2. Norm bounds -/

























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

theorem integrableOn_rpow_exp {a b : ℝ} (ha : -1 < a) (hb : 0 < b) :
    IntegrableOn (fun ρ : ℝ => ρ ^ a * Real.exp (-(b * ρ))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) ha (by norm_num) hb
  refine this.congr_fun (fun ρ _ => ?_) measurableSet_Ioi
  simp [Real.rpow_one, neg_mul]

theorem norm_ofReal_cpow {ρ : ℝ} (hρ : 0 < ρ) (s : ℂ) : ‖(ρ : ℂ) ^ s‖ = ρ ^ s.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hρ s

theorem one_add_I_ne_zero : (1 + I : ℂ) ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this

theorem one_sub_I_ne_zero : (1 - I : ℂ) ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this

/-! ## 2. Branch bookkeeping -/







/-! ## 3. The complex-scaled Gamma integral -/



/-! ## 4. The Mellin step (Fubini) -/





theorem cpow_mul_cpow_neg_one_add_I (s : ℂ) : (1 + I) ^ s * (1 + I) ^ (-s) = 1 := by
  rw [Complex.cpow_neg, mul_inv_cancel₀]
  rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => one_add_I_ne_zero h.1







/-! ## 5. Splitting the Mordell kernel -/

theorem norm_exp_one_add_I_mul (ρ : ℝ) : ‖cexp ((1 + I) * ρ)‖ = Real.exp ρ := by
  rw [Complex.norm_exp]; simp

theorem exp_one_add_I_ne_one {ρ : ℝ} (hρ : 0 < ρ) : cexp ((1 + I) * ρ) ≠ 1 := by
  intro h
  have := norm_exp_one_add_I_mul ρ
  rw [h, norm_one] at this
  have h2 : (1 : ℝ) < Real.exp ρ := Real.one_lt_exp_iff.mpr hρ
  linarith



/-! ## 6. The Bose integral -/





/-! ## 7. The chi-side kernel -/





theorem rsH_ray (r : ℝ) : rsH ((r : ℂ) * (1 - I)) = rsE (2 * π * r) := by
  unfold rsH rsD rsE
  have hpi := pi_ne_zero'
  push_cast
  congr 1
  · congr 1
    field_simp
    linear_combination (-8 * (r : ℂ) ^ 2) * I_sq
  · congr 1
    · congr 1; linear_combination (-(↑π * (r : ℂ))) * I_sq
    · congr 1; linear_combination (↑π * (r : ℂ)) * I_sq

theorem ofReal_mul_cpow {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    ((r : ℂ) * z) ^ w = (r : ℂ) ^ w * z ^ w := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hr0 hz), Complex.cpow_def_of_ne_zero hr0,
    Complex.cpow_def_of_ne_zero hz, Complex.log_ofReal_mul hr hz, ← Complex.exp_add,
    Complex.ofReal_log hr.le]
  congr 1; ring

theorem cpow_mul_cpow_neg {z : ℂ} (hz : z ≠ 0) (s : ℂ) : z ^ s * z ^ (-s) = 1 := by
  rw [Complex.cpow_neg, mul_inv_cancel₀]
  rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hz h.1

theorem integral_Epart (s : ℂ) :
    ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (s - 1) * rsE ρ = (2 * ↑π) ^ s * (1 - I) ^ (-s) * rsHR s := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have hpi0 : (2 * ↑π : ℂ) ≠ 0 := by
    have := pi_ne_zero'; exact mul_ne_zero two_ne_zero this
  have h1 : rsHR s = (1 - I) ^ s * ∫ r in Ioi (0 : ℝ), (r : ℂ) ^ (s - 1) * rsE (2 * π * r) := by
    unfold rsHR
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    rw [rsH_ray, ofReal_mul_cpow hr one_sub_I_ne_zero]
    have h : (1 - I) ^ (s - 1) * (1 - I) = (1 - I) ^ s := by
      rw [Complex.cpow_sub _ _ one_sub_I_ne_zero, Complex.cpow_one,
        div_mul_cancel₀ _ one_sub_I_ne_zero]
    linear_combination (rsE (2 * π * r) * (r : ℂ) ^ (s - 1)) * h
  have h2 : ∫ r in Ioi (0 : ℝ), (r : ℂ) ^ (s - 1) * rsE (2 * π * r) =
      (2 * ↑π) ^ (-s) * ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (s - 1) * rsE ρ := by
    have hsub := integral_comp_mul_left_Ioi (fun ρ : ℝ => (ρ : ℂ) ^ (s - 1) * rsE ρ) 0 hpi
    rw [mul_zero] at hsub
    have hpt : ∀ r ∈ Ioi (0 : ℝ), (r : ℂ) ^ (s - 1) * rsE (2 * π * r) =
        (2 * ↑π) ^ (1 - s) * ((((2 * π * r : ℝ)) : ℂ) ^ (s - 1) * rsE (2 * π * r)) := by
      intro r hr
      rw [show (((2 * π * r : ℝ)) : ℂ) = (((2 * π : ℝ)) : ℂ) * (r : ℂ) by push_cast; ring,
        Complex.mul_cpow_ofReal_nonneg hpi.le (le_of_lt hr)]
      have hc : (2 * ↑π : ℂ) ^ (1 - s) * (((2 * π : ℝ)) : ℂ) ^ (s - 1) = 1 := by
        push_cast
        rw [← Complex.cpow_add _ _ hpi0, show 1 - s + (s - 1) = 0 by ring, Complex.cpow_zero]
      linear_combination (-((r : ℂ) ^ (s - 1) * rsE (2 * π * r))) * hc
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, hsub, Complex.real_smul]
    push_cast
    rw [← mul_assoc]
    congr 1
    rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hpi0]
    congr 1; ring
  rw [h1, h2]
  have e1 := cpow_mul_cpow_neg one_sub_I_ne_zero s
  have e2 := cpow_mul_cpow_neg hpi0 s
  linear_combination (-(∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (s - 1) * rsE ρ)) *
    ((2 * ↑π) ^ s * (2 * ↑π) ^ (-s) * e1 + e2)

/-! ## 8. Integrability of the two pieces on (0, oo) -/

theorem le_exp_sub_exp {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ρ ≤ Real.exp (ρ / 2) - Real.exp (-(ρ / 2)) := by
  have h := Real.self_le_sinh_iff.mpr (by linarith : 0 ≤ ρ / 2)
  rw [Real.sinh_eq] at h
  linarith

theorem norm_exp_half_sub_ge {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ρ ≤ ‖cexp ((1 + I) * ρ / 2) - cexp (-((1 + I) * ρ / 2))‖ := by
  have h1 : ‖cexp ((1 + I) * ρ / 2)‖ = Real.exp (ρ / 2) := by rw [Complex.norm_exp]; simp
  have h2 : ‖cexp (-((1 + I) * ρ / 2))‖ = Real.exp (-(ρ / 2)) := by rw [Complex.norm_exp]; simp
  have := norm_sub_norm_le (cexp ((1 + I) * ρ / 2)) (cexp (-((1 + I) * ρ / 2)))
  rw [h1, h2] at this
  linarith [le_exp_sub_exp hρ]

theorem norm_exp_sub_one_ge {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ρ * Real.exp (ρ / 2) ≤ ‖cexp ((1 + I) * ρ) - 1‖ := by
  have h1 := norm_sub_norm_le (cexp ((1 + I) * ρ)) 1
  rw [norm_exp_one_add_I_mul, norm_one] at h1
  have h2 := le_exp_sub_exp hρ
  have h3 : Real.exp ρ - 1 = Real.exp (ρ / 2) * (Real.exp (ρ / 2) - Real.exp (-(ρ / 2))) := by
    rw [mul_sub, ← Real.exp_add, ← Real.exp_add, show ρ / 2 + ρ / 2 = ρ by ring,
      show ρ / 2 + -(ρ / 2) = 0 by ring, Real.exp_zero]
  have h4 : ρ * Real.exp (ρ / 2) ≤ Real.exp ρ - 1 := by
    rw [h3, mul_comm]; exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  linarith

theorem integrableOn_bose {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun ρ : ℝ => (ρ : ℂ) ^ (s - 1) * (1 / (cexp ((1 + I) * ρ) - 1))) (Ioi 0) := by
  refine (integrableOn_rpow_exp (a := s.re - 2) (b := 1 / 2) (by linarith) (by norm_num)).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro ρ hρ
    have hne : cexp ((1 + I) * ρ) - 1 ≠ 0 := sub_ne_zero.mpr (exp_one_add_I_ne_one hρ)
    exact (((continuousAt_cpow_const (ofReal_mem_slitPlane.mpr hρ)).comp
      Complex.continuous_ofReal.continuousAt).mul
      (continuousAt_const.div (by fun_prop) hne)).continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun ρ hρ => ?_)
    have hρ' : (0 : ℝ) < ρ := hρ
    have hden := norm_exp_sub_one_ge hρ'.le
    have hpos : 0 < ρ * Real.exp (ρ / 2) := by positivity
    rw [norm_mul, norm_ofReal_cpow hρ', norm_div, norm_one]
    have hq : 1 / ‖cexp ((1 + I) * ρ) - 1‖ ≤ 1 / (ρ * Real.exp (ρ / 2)) :=
      one_div_le_one_div_of_le hpos hden
    have hpow : ρ ^ (s - 1).re * (1 / (ρ * Real.exp (ρ / 2))) =
        ρ ^ (s.re - 2) * Real.exp (-(1 / 2 * ρ)) := by
      rw [Complex.sub_re, Complex.one_re, show s.re - 2 = (s.re - 1) - 1 by ring,
        Real.rpow_sub_one hρ'.ne' (s.re - 1), show -(1 / 2 * ρ) = -(ρ / 2) by ring, Real.exp_neg]
      ring
    calc ρ ^ (s - 1).re * (1 / ‖cexp ((1 + I) * ρ) - 1‖)
        ≤ ρ ^ (s - 1).re * (1 / (ρ * Real.exp (ρ / 2))) :=
          mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg hρ'.le _)
      _ = _ := hpow

theorem integrableOn_Epart {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun ρ : ℝ => (ρ : ℂ) ^ (s - 1) * rsE ρ) (Ioi 0) := by
  have hb : (0 : ℝ) < 1 / (2 * π) := by positivity
  refine (integrableOn_rpow_mul_exp_neg_mul_sq hb (s := s.re - 2) (by linarith)).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro ρ hρ
    have hne : cexp ((1 + I) * ρ / 2) - cexp (-((1 + I) * ρ / 2)) ≠ 0 := by
      intro h
      have := norm_exp_half_sub_ge (le_of_lt hρ)
      rw [h, norm_zero] at this
      exact absurd this (not_le.mpr hρ)
    unfold rsE
    exact (((continuousAt_cpow_const (ofReal_mem_slitPlane.mpr hρ)).comp
      Complex.continuous_ofReal.continuousAt).mul
      ((by fun_prop : ContinuousAt (fun ρ : ℝ => cexp (I * ((1 + I) * ρ) ^ 2 / (4 * ↑π))) ρ).div
        (by fun_prop) hne)).continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun ρ hρ => ?_)
    have hρ' : (0 : ℝ) < ρ := hρ
    have hden := norm_exp_half_sub_ge hρ'.le
    have hnum : ‖cexp (I * ((1 + I) * ρ) ^ 2 / (4 * ↑π))‖ = Real.exp (-(1 / (2 * π)) * ρ ^ 2) := by
      rw [Complex.norm_exp]
      congr 1
      have hpi := Real.pi_pos
      simp [pow_two, mul_re, mul_im, div_re]
      field_simp
      ring
    unfold rsE
    rw [norm_mul, norm_ofReal_cpow hρ', norm_div, hnum]
    have hq : Real.exp (-(1 / (2 * π)) * ρ ^ 2) /
        ‖cexp ((1 + I) * ρ / 2) - cexp (-((1 + I) * ρ / 2))‖ ≤
        Real.exp (-(1 / (2 * π)) * ρ ^ 2) / ρ :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le hρ' hden
    calc ρ ^ (s - 1).re * (Real.exp (-(1 / (2 * π)) * ρ ^ 2) /
          ‖cexp ((1 + I) * ρ / 2) - cexp (-((1 + I) * ρ / 2))‖)
        ≤ ρ ^ (s - 1).re * (Real.exp (-(1 / (2 * π)) * ρ ^ 2) / ρ) :=
          mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg hρ'.le _)
      _ = ρ ^ (s.re - 2) * Real.exp (-(1 / (2 * π)) * ρ ^ 2) := by
          rw [Complex.sub_re, Complex.one_re, show s.re - 2 = (s.re - 1) - 1 by ring,
            Real.rpow_sub_one hρ'.ne' (s.re - 1)]
          ring

/-! ## 9. The Mellin identity -/

/-- **The Mellin identity** (Re s > 1, 0 < c < 1):
    Gamma(s) lineUp c (rsG x^(-s)) = -Gamma(s) zeta(s) + (2 pi)^s (1+i)^s (1-i)^(-s) rsHR s. -/
theorem mellin_identity {c : ℝ} (hc : 0 < c) (hc1 : c < 1) {s : ℂ} (hs : 1 < s.re) :
    Gamma s * lineUp c (fun x => rsG x * x ^ (-s)) =
      -(Gamma s * riemannZeta s) + (2 * ↑π) ^ s * (1 + I) ^ s * (1 - I) ^ (-s) * rsHR s := by
  rw [mellin_step hc hc1 (by linarith)]
  have hsplit : ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (s - 1) * rsK c ((1 + I) * ρ) =
      (∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (s - 1) * rsE ρ) -
        ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (s - 1) * (1 / (cexp ((1 + I) * ρ) - 1)) := by
    rw [← integral_sub (integrableOn_Epart hs) (integrableOn_bose hs)]
    refine setIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => ?_)
    rw [rsK_split hc hc1 hρ]; unfold rsE; ring
  rw [hsplit, integral_bose hs, integral_Epart s]
  have h1 := cpow_mul_cpow_neg_one_add_I s
  linear_combination (-(Gamma s * riemannZeta s)) * h1

end RSInt

end

/-  RS_Fold.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 4:
    the chi-side line.  Mathlib-only (imports `RS_Mellin`).

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `norm_cpow_le_exp` : ‖x^w‖ <= e^{pi |Im w|} e^{Re w ‖x‖} for Re w >= 0 (growth of x^w).
      * `continuousAt_rsH_cpow_zero` : for Re s > 2 the chi-side integrand rsH(x) x^(s-1) is
        continuous at the pole x = 0 of rsH (removable via dslope, value 0).
      * `lineDn_zero_fold` : FOLDING.  For Re s > 2 the chi-side integral along the line through 0
        is (1 + e^{i pi s}) times the half-line integral:
            lineDn 0 (rsH x^(s-1)) = (1 + e^{i pi s}) rsHR s
        (rsH is odd, and (-x)^(s-1) = x^(s-1) e^{i pi (s-1)} on that line).
      * `lineDn_zero_eq` : the line through 0 may be moved to any c in (0, 1) (strip Cauchy; the
        pole at 0 sits on the boundary and is harmless for Re s > 2).
      * `lineDn_eq_fold` : lineDn c (rsH x^(s-1)) = (1 + e^{i pi s}) rsHR s, 0 < c < 1, Re s > 2.

    conjecture1_proved = False.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

namespace RSInt

/-! ## 1. Growth of `x^w` -/



/-! ## 2. Continuity of the chi-side integrand at 0 -/





/-! ## 3. Folding the line through 0 -/

















/-! ## 4. Moving the chi-side line off the pole -/



/-- The chi-side line through any `c ∈ (0,1)`, folded: for Re s > 2,
    `lineDn c (rsH x^(s-1)) = (1 + e^{i pi s}) rsHR s`. -/
theorem lineDn_eq_fold {s : ℂ} (hs : 2 < s.re) {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    lineDn c (fun x => rsH x * x ^ (s - 1)) = (1 + cexp (↑π * I * s)) * rsHR s := by
  rw [← lineDn_zero_eq hs hc hc1, lineDn_zero_fold hs]

end RSInt

end

/-  RS_Entire.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 5:
    holomorphy in `s` of the two Riemann-Siegel line integrals, and the chi factor.
    Mathlib-only (imports `RS_Fold`).

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `differentiable_integral_cpow` : a generic parametric-holomorphy lemma:
            s |-> int W(v) X(v)^s dv   is entire
        for continuous W with a Gaussian tail and a continuous line X in the slit plane with
        m <= |X v| <= alpha + beta |v|.
      * `differentiable_rsA`, `differentiable_rsB` : s |-> lineUp c (rsG x^(-s)) and
        s |-> lineDn c (rsH x^(s-1)) are entire for every c > 0 that is not an integer.
      * `rsChi s = pi^(s - 1/2) Gamma((1-s)/2) / Gamma(s/2)`, holomorphic off {1, 3, 5, ...}
        (`differentiableAt_rsChi`), with the Gamma-function identity
            rsChi s * Gamma s * (2 cos(pi s / 2)) = (2 pi)^s     (Re s > 0)
        (`rsChi_mul_Gamma_cos`, reflection + duplication).

    conjecture1_proved = False.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

namespace RSInt

/-! ## 1. A generic parametric-holomorphy lemma -/







/-! ## 2. The two Riemann-Siegel line integrals are entire in `s` -/



















/-! ## 3. The chi factor -/







theorem one_add_I_cpow_mul (s : ℂ) : (1 + I) ^ s * (1 - I) ^ (-s) = cexp (↑π * I * s / 2) := by
  have hne : (1 - I : ℂ) ≠ 0 := one_sub_I_ne_zero
  have hre : 0 < (1 - I : ℂ).re := by simp
  have harg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have hlog : Complex.log (1 + I) = Complex.log I + Complex.log (1 - I) := by
    have h : (1 + I : ℂ) = I * (1 - I) := by ring_nf; rw [I_sq]; ring
    rw [h]
    refine (Complex.log_mul_eq_add_log_iff I_ne_zero hne).mpr ⟨?_, ?_⟩
    · rw [Complex.arg_I]; linarith [(abs_lt.mp harg).1, Real.pi_pos]
    · rw [Complex.arg_I]; linarith [(abs_lt.mp harg).2, Real.pi_pos]
  rw [Complex.cpow_def_of_ne_zero one_add_I_ne_zero, Complex.cpow_def_of_ne_zero hne, hlog,
    Complex.log_I, ← Complex.exp_add]
  congr 1; ring

theorem one_add_exp_eq (s : ℂ) :
    1 + cexp (↑π * I * s) = 2 * Complex.cos (↑π * s / 2) * cexp (↑π * I * s / 2) := by
  rw [Complex.two_cos, add_mul, ← Complex.exp_add, ← Complex.exp_add]
  rw [show ↑π * s / 2 * I + ↑π * I * s / 2 = ↑π * I * s by ring,
    show -(↑π * s / 2) * I + ↑π * I * s / 2 = 0 by ring, Complex.exp_zero]
  ring

theorem cos_ne_zero_of_one_add_exp {s : ℂ} (h : 1 + cexp (↑π * I * s) ≠ 0) :
    Complex.cos (↑π * s / 2) ≠ 0 := by
  intro hc; apply h; rw [one_add_exp_eq, hc]; ring

/-- The chi factor in the form produced by the Mellin/folding computation. -/
theorem rsChi_eq {s : ℂ} (hs : 0 < s.re) (h : 1 + cexp (↑π * I * s) ≠ 0) :
    rsChi s = (2 * ↑π) ^ s * (1 + I) ^ s * (1 - I) ^ (-s) / (Gamma s * (1 + cexp (↑π * I * s))) := by
  have hcos := cos_ne_zero_of_one_add_exp h
  have hG : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  have hE : cexp (↑π * I * s / 2) ≠ 0 := Complex.exp_ne_zero _
  rw [eq_div_iff (mul_ne_zero hG h), mul_assoc ((2 * (π : ℂ)) ^ s), one_add_I_cpow_mul,
    one_add_exp_eq, ← rsChi_mul_Gamma_cos hs hcos]
  ring

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




theorem solution {s : ℂ} (hs : 2 < s.re) (h : 1 + cexp (↑π * I * s) ≠ 0)
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    riemannZeta s = -lineUp c (fun x => rsG x * x ^ (-s)) +
      rsChi s * lineDn c (fun x => rsH x * x ^ (s - 1)) := by
  have hM := mellin_identity hc hc1 (s := s) (by linarith)
  have hB := lineDn_eq_fold hs hc hc1
  have hχ := rsChi_eq (s := s) (by linarith) h
  have hG : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  rw [hB, hχ]
  set K := (2 * (π : ℂ)) ^ s * (1 + I) ^ s * (1 - I) ^ (-s) with hK
  have e : K / (Gamma s * (1 + cexp (↑π * I * s))) * ((1 + cexp (↑π * I * s)) * rsHR s) =
      K * rsHR s / Gamma s := by
    rw [div_mul_eq_mul_div, show K * ((1 + cexp (↑π * I * s)) * rsHR s) =
      K * rsHR s * (1 + cexp (↑π * I * s)) by ring, mul_div_mul_right _ _ h]
  rw [e, eq_comm, ← sub_eq_zero]
  have : -lineUp c (fun x => rsG x * x ^ (-s)) + K * rsHR s / Gamma s - riemannZeta s =
      (K * rsHR s - Gamma s * lineUp c (fun x => rsG x * x ^ (-s)) - Gamma s * riemannZeta s) /
        Gamma s := by
    field_simp
    ring
  rw [this, hM]
  simp

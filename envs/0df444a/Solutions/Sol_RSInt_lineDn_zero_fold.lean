-- Prove2me | solution 1 for RSInt.lineDn_zero_fold
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:04:25.382878+00:00
-- url     : https://prove2.me/submissions/3772a220-ae18-4d5c-82fc-991220d33630

import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_continuousAt_rsH_cpow_zero
import Theorems.Thm_RSInt_integrable_of_continuous_of_tail
import Theorems.Thm_RSInt_norm_rsH_mul_le
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





















theorem norm_one_sub_I : ‖(1 - I : ℂ)‖ = Real.sqrt 2 := by
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





theorem exp_neg_piI : cexp (-(↑π * I)) = -1 := by
  rw [Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num







/-! ## 2. Norm bounds -/

























/-! ## 3. The Fresnel line integral -/











/-! ## 4. Gaussian tails, line integrability, and the strip wrappers -/























/-! ## 5. Linearity and translation of line integrals -/













/-! ## 6. Holomorphy of the kernels off the integers -/

theorem rsD_ne_zero_of_ne {x : ℂ} (h : ∀ n : ℤ, x ≠ n) : rsD x ≠ 0 := by
  intro h0; obtain ⟨n, hn⟩ := (rsD_eq_zero_iff x).mp h0; exact h n hn



theorem differentiableAt_rsH {x : ℂ} (h : rsD x ≠ 0) : DifferentiableAt ℂ rsH x := by
  unfold rsH
  exact ((by fun_prop : Differentiable ℂ (fun x : ℂ => cexp (-(↑π * I * x ^ 2)))) x).div
    (differentiable_rsD x) h







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







theorem one_sub_I_ne_zero : (1 - I : ℂ) ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this

/-! ## 2. Branch bookkeeping -/







/-! ## 3. The complex-scaled Gamma integral -/



/-! ## 4. The Mellin step (Fubini) -/













/-! ## 5. Splitting the Mordell kernel -/







/-! ## 6. The Bose integral -/





/-! ## 7. The chi-side kernel -/







theorem ofReal_mul_cpow {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    ((r : ℂ) * z) ^ w = (r : ℂ) ^ w * z ^ w := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hr0 hz), Complex.cpow_def_of_ne_zero hr0,
    Complex.cpow_def_of_ne_zero hz, Complex.log_ofReal_mul hr hz, ← Complex.exp_add,
    Complex.ofReal_log hr.le]
  congr 1; ring





/-! ## 8. Integrability of the two pieces on (0, oo) -/











/-! ## 9. The Mellin identity -/



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

theorem norm_cpow_le_exp {w : ℂ} (hw : 0 ≤ w.re) (x : ℂ) :
    ‖x ^ w‖ ≤ Real.exp (π * |w.im|) * Real.exp (w.re * ‖x‖) := by
  have h1 : 1 ≤ Real.exp (π * |w.im|) * Real.exp (w.re * ‖x‖) := by
    rw [← Real.exp_add]; exact Real.one_le_exp (by positivity)
  rcases eq_or_ne x 0 with rfl | hx
  · rcases eq_or_ne w 0 with rfl | hw0
    · simp only [Complex.cpow_zero, norm_one]; exact h1
    · rw [Complex.zero_cpow hw0, norm_zero]; positivity
  · rw [Complex.norm_cpow_of_ne_zero hx]
    have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hA : ‖x‖ ^ w.re ≤ Real.exp (w.re * ‖x‖) := by
      rw [Real.rpow_def_of_pos hpos]
      apply Real.exp_le_exp.mpr
      have := Real.log_le_sub_one_of_pos hpos
      nlinarith
    have hB : 1 / Real.exp (x.arg * w.im) ≤ Real.exp (π * |w.im|) := by
      rw [one_div, ← Real.exp_neg]
      apply Real.exp_le_exp.mpr
      have h2 := Complex.abs_arg_le_pi x
      have h3 : -(x.arg * w.im) ≤ |x.arg * w.im| := neg_le_abs _
      rw [abs_mul] at h3
      nlinarith [abs_nonneg w.im, abs_nonneg x.arg]
    calc ‖x‖ ^ w.re / Real.exp (x.arg * w.im)
        = ‖x‖ ^ w.re * (1 / Real.exp (x.arg * w.im)) := by ring
      _ ≤ Real.exp (w.re * ‖x‖) * Real.exp (π * |w.im|) :=
          mul_le_mul hA hB (by positivity) (Real.exp_pos _).le
      _ = Real.exp (π * |w.im|) * Real.exp (w.re * ‖x‖) := by ring

/-! ## 2. Continuity of the chi-side integrand at 0 -/

theorem rsH_neg (x : ℂ) : rsH (-x) = -rsH x := by
  unfold rsH rsD
  rw [neg_sq, show ↑π * I * -x = -(↑π * I * x) by ring, neg_neg, ← neg_sub, div_neg]



/-! ## 3. Folding the line through 0 -/

theorem log_neg_one_sub_I : Complex.log (-(1 - I)) = Complex.log (1 - I) + ↑π * I := by
  have hne : (1 - I : ℂ) ≠ 0 := one_sub_I_ne_zero
  have him : (1 - I : ℂ).im < 0 := by simp
  apply Complex.ext
  · rw [Complex.add_re, Complex.log_re, Complex.log_re, norm_neg]; simp
  · rw [Complex.log_im, Complex.add_im, Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg him]
    simp

theorem cpow_neg_line {r : ℝ} (hr : 0 < r) (w : ℂ) :
    (((-r : ℝ) : ℂ) * (1 - I)) ^ w = (((r : ℝ) : ℂ) * (1 - I)) ^ w * cexp (↑π * I * w) := by
  have h1 : (((-r : ℝ) : ℂ) * (1 - I)) = (r : ℂ) * (-(1 - I)) := by push_cast; ring
  have hne : -(1 - I : ℂ) ≠ 0 := neg_ne_zero.mpr one_sub_I_ne_zero
  rw [h1, ofReal_mul_cpow hr hne, ofReal_mul_cpow hr one_sub_I_ne_zero,
    Complex.cpow_def_of_ne_zero hne, Complex.cpow_def_of_ne_zero one_sub_I_ne_zero,
    log_neg_one_sub_I, mul_assoc, ← Complex.exp_add]
  congr 2; ring



theorem rsFdn_neg {s : ℂ} {r : ℝ} (hr : 0 < r) : rsFdn s (-r) = cexp (↑π * I * s) * rsFdn s r := by
  unfold rsFdn
  rw [cpow_neg_line hr, show ((-r : ℝ) : ℂ) * (1 - I) = -((r : ℂ) * (1 - I)) by push_cast; ring,
    rsH_neg]
  have : cexp (↑π * I * (s - 1)) = -cexp (↑π * I * s) := by
    rw [show ↑π * I * (s - 1) = ↑π * I * s + -(↑π * I) by ring, Complex.exp_add, exp_neg_piI]
    ring
  rw [this]; ring

theorem continuous_rsFdn {s : ℂ} (hs : 2 < s.re) : Continuous (rsFdn s) := by
  rw [continuous_iff_continuousAt]
  intro v
  unfold rsFdn
  refine ContinuousAt.mul ?_ continuousAt_const
  rcases eq_or_ne v 0 with rfl | hv
  · have h := continuousAt_rsH_cpow_zero hs
    have h2 : ContinuousAt (fun v : ℝ => (v : ℂ) * (1 - I)) 0 := by fun_prop
    have h3 : ((0 : ℝ) : ℂ) * (1 - I) = 0 := by simp
    rw [← h3] at h
    exact ContinuousAt.comp (g := fun x => rsH x * x ^ (s - 1))
      (f := fun v : ℝ => (v : ℂ) * (1 - I)) h h2
  · have hx : ((v : ℂ) * (1 - I)).im ≠ 0 := by simp; exact hv
    have hD : rsD ((v : ℂ) * (1 - I)) ≠ 0 := by
      refine rsD_ne_zero_of_ne fun n hn => hx ?_
      rw [hn]; simp
    have hslit : (v : ℂ) * (1 - I) ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inr hx)
    have h1 : ContinuousAt (fun x => rsH x * x ^ (s - 1)) ((v : ℂ) * (1 - I)) :=
      (differentiableAt_rsH hD).continuousAt.mul (continuousAt_cpow_const hslit)
    have h2 : ContinuousAt (fun v : ℝ => (v : ℂ) * (1 - I)) v := by fun_prop
    exact ContinuousAt.comp (g := fun x => rsH x * x ^ (s - 1))
      (f := fun v : ℝ => (v : ℂ) * (1 - I)) h1 h2

theorem growth_cpow_sub_one {s : ℂ} (hs : 1 ≤ s.re) (x : ℂ) :
    ‖x ^ (s - 1)‖ ≤ Real.exp (π * |s.im|) * Real.exp ((s.re - 1) * ‖x‖) := by
  have := norm_cpow_le_exp (w := s - 1) (by simp; linarith) x
  simpa using this

theorem integrable_rsFdn {s : ℂ} (hs : 2 < s.re) : Integrable (rsFdn s) := by
  refine integrable_of_continuous_of_tail (continuous_rsFdn hs) (a := 2 * π) (R := 1)
    (C := (|Real.exp (π * |s.im|)| * Real.exp (|s.re - 1| * (|(0 : ℝ)| + |(0 : ℝ)|))) * Real.sqrt 2)
    (b := 2 * π * (|(0 : ℝ)| + |(0 : ℝ)|) + 2 * |s.re - 1|) (by positivity) (fun v hv => ?_)
  have hx : ((v : ℂ) * (1 - I)).re + ((v : ℂ) * (1 - I)).im ∈ Icc (0 : ℝ) 0 := by simp
  have him : ((v : ℂ) * (1 - I)).im = -v := by simp
  have h1 : 1 ≤ |((v : ℂ) * (1 - I)).im| := by rw [him, abs_neg]; exact hv
  have hb := norm_rsH_mul_le (ψ := fun x => x ^ (s - 1)) hx h1
    (growth_cpow_sub_one (by linarith) _)
  unfold rsFdn
  rw [norm_mul, norm_one_sub_I]
  rw [him, abs_neg, neg_sq] at hb
  calc ‖rsH ((v : ℂ) * (1 - I)) * ((v : ℂ) * (1 - I)) ^ (s - 1)‖ * Real.sqrt 2
      ≤ (|Real.exp (π * |s.im|)| * Real.exp (|s.re - 1| * (|(0 : ℝ)| + |(0 : ℝ)|))) *
          Real.exp (-(2 * π) * v ^ 2 + (2 * π * (|(0 : ℝ)| + |(0 : ℝ)|) + 2 * |s.re - 1|) * |v|) *
          Real.sqrt 2 := mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg 2)
    _ = _ := by ring



/-! ## 4. Moving the chi-side line off the pole -/





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

section
namespace RSInt
end RSInt
open RSInt

/-! ## 1. Growth of `x^w` -/



/-! ## 2. Continuity of the chi-side integrand at 0 -/





/-! ## 3. Folding the line through 0 -/
















theorem solution {s : ℂ} (hs : 2 < s.re) :
    lineDn 0 (fun x => rsH x * x ^ (s - 1)) = (1 + cexp (↑π * I * s)) * rsHR s := by
  have hL : lineDn 0 (fun x => rsH x * x ^ (s - 1)) = ∫ v : ℝ, rsFdn s v := by
    unfold lineDn rsFdn; congr 1; ext v; simp
  have hint := integrable_rsFdn hs
  rw [hL, ← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn]
  have hIic : ∫ v in Iic (0 : ℝ), rsFdn s v = cexp (↑π * I * s) * rsHR s := by
    rw [← neg_zero, ← integral_comp_neg_Ioi]
    unfold rsHR
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    rw [rsFdn_neg hr]; unfold rsFdn; ring
  have hIoi : ∫ v in Ioi (0 : ℝ), rsFdn s v = rsHR s := by
    unfold rsHR rsFdn; rfl
  rw [hIic, hIoi]; ring

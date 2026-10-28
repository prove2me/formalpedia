-- Prove2me | solution 1 for RSInt.norm_rsJ_le
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:15:33.884443+00:00
-- url     : https://prove2.me/submissions/bfe54e46-5e5c-4f15-8cf9-ad820799c05e

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_integrable_of_continuous_of_tail
import Theorems.Thm_RSInt_lineUp_eq_of_strip
import Theorems.Thm_RSInt_two_le_norm_rsD_midline
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

theorem exp_quad_le (a b v : ℝ) (ha : 0 < a) :
    Real.exp (-a * v ^ 2 + b * |v|) ≤ Real.exp (b ^ 2 / (2 * a)) * Real.exp (-(a / 2) * v ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h2a : 0 < 2 * a := by positivity
  have key : 2 * a * (-a * v ^ 2 + b * |v|) ≤ 2 * a * (b ^ 2 / (2 * a) + -(a / 2) * v ^ 2) := by
    rw [mul_add (2 * a) (b ^ 2 / (2 * a)), mul_div_cancel₀ _ h2a.ne']
    nlinarith [sq_nonneg (a * |v| - b), show a ^ 2 * |v| ^ 2 = a ^ 2 * v ^ 2 by rw [sq_abs]]
  exact le_of_mul_le_mul_left key h2a





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





/-- On the slanted strip `c1 <= Re x - Im x <= c2`, `‖x‖ <= 2 |Im x| + D`, `D = |c1| + |c2|`. -/
theorem norm_le_of_upStrip {x : ℂ} {c₁ c₂ : ℝ} (hx : x.re - x.im ∈ Icc c₁ c₂) :
    ‖x‖ ≤ 2 * |x.im| + (|c₁| + |c₂|) := by
  have h1 := Complex.norm_le_abs_re_add_abs_im x
  have hd : |x.re - x.im| ≤ |c₁| + |c₂| := by
    rw [abs_le]; constructor
    · linarith [hx.1, neg_abs_le c₁, abs_nonneg c₂]
    · linarith [hx.2, le_abs_self c₂, abs_nonneg c₁]
  have h2 : |x.re| ≤ |x.im| + |x.re - x.im| := by
    calc |x.re| = |x.im + (x.re - x.im)| := by ring_nf
      _ ≤ |x.im| + |x.re - x.im| := abs_add_le _ _
  linarith







/-! ## 3. The Fresnel line integral -/











/-! ## 4. Gaussian tails, line integrability, and the strip wrappers -/

theorem gauss_tail_small {C a b : ℝ} (ha : 0 < a) :
    ∀ ε > 0, ∃ Y : ℝ, 1 ≤ Y ∧ ∀ y : ℝ, Y ≤ |y| → C * Real.exp (-a * y ^ 2 + b * |y|) ≤ ε := by
  intro ε hε
  set K := Real.exp (b ^ 2 / (2 * a)) with hK
  set M := |C| * K + 1 with hM
  have hMpos : 0 < M := by positivity
  refine ⟨max 1 (2 / a * |Real.log (M / ε)|), le_max_left _ _, fun y hy => ?_⟩
  have hy1 : 1 ≤ |y| := le_trans (le_max_left _ _) hy
  have hy2 : 2 / a * |Real.log (M / ε)| ≤ |y| := le_trans (le_max_right _ _) hy
  have h1 : C * Real.exp (-a * y ^ 2 + b * |y|) ≤ |C| * (K * Real.exp (-(a / 2) * y ^ 2)) := by
    calc C * Real.exp (-a * y ^ 2 + b * |y|) ≤ |C| * Real.exp (-a * y ^ 2 + b * |y|) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
      _ ≤ |C| * (K * Real.exp (-(a / 2) * y ^ 2)) :=
          mul_le_mul_of_nonneg_left (exp_quad_le a b y ha) (abs_nonneg C)
  have h2 : Real.exp (-(a / 2) * y ^ 2) ≤ Real.exp (-(a / 2) * |y|) := by
    apply Real.exp_le_exp.mpr
    have : |y| ≤ y ^ 2 := by
      rw [← sq_abs]; nlinarith
    nlinarith
  have h3 : Real.exp (-(a / 2) * |y|) ≤ ε / M := by
    have hl : |Real.log (M / ε)| ≤ a / 2 * |y| := by
      have := mul_le_mul_of_nonneg_left hy2 (le_of_lt (half_pos ha))
      rwa [← mul_assoc, show a / 2 * (2 / a) = 1 by field_simp, one_mul] at this
    calc Real.exp (-(a / 2) * |y|) ≤ Real.exp (-Real.log (M / ε)) := by
          apply Real.exp_le_exp.mpr
          have := le_abs_self (Real.log (M / ε))
          nlinarith
      _ = ε / M := by
          rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  have hK0 : 0 ≤ K := (Real.exp_pos _).le
  calc C * Real.exp (-a * y ^ 2 + b * |y|) ≤ |C| * (K * Real.exp (-(a / 2) * y ^ 2)) := h1
    _ ≤ M * Real.exp (-(a / 2) * |y|) := by
        have : |C| * (K * Real.exp (-(a / 2) * y ^ 2)) ≤ |C| * K * Real.exp (-(a / 2) * |y|) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
        have h4 : |C| * K * Real.exp (-(a / 2) * |y|) ≤ M * Real.exp (-(a / 2) * |y|) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
        linarith
    _ ≤ M * (ε / M) := mul_le_mul_of_nonneg_left h3 hMpos.le
    _ = ε := by field_simp



theorem lineUp_pt_im (c v : ℝ) : ((c : ℂ) + v * (1 + I)).im = v := by simp





theorem integrable_lineUp {F : ℂ → ℂ} {c₁ c₂ c : ℝ} (hc : c ∈ Icc c₁ c₂)
    (hcont : ContinuousOn F {x : ℂ | x.re - x.im ∈ Icc c₁ c₂})
    {C a b : ℝ} (ha : 0 < a)
    (hbound : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → 1 ≤ |x.im| →
      ‖F x‖ ≤ C * Real.exp (-a * x.im ^ 2 + b * |x.im|)) :
    Integrable (fun v : ℝ => F (c + v * (1 + I))) := by
  have hmem : ∀ v : ℝ, ((c : ℂ) + v * (1 + I)) ∈ {x : ℂ | x.re - x.im ∈ Icc c₁ c₂} := by
    intro v
    simp only [mem_setOf_eq]
    have e : ((c : ℂ) + v * (1 + I)).re - ((c : ℂ) + v * (1 + I)).im = c := by simp
    rw [e]; exact hc
  refine integrable_of_continuous_of_tail (a := a) (b := b) (C := C) (R := 1)
    (hcont.comp_continuous (by fun_prop) hmem) ha (fun v hv => ?_)
  have := hbound _ (hmem v) (by rw [lineUp_pt_im]; exact hv)
  rwa [lineUp_pt_im] at this



/-- `lineUp_eq_of_strip` with the integrability and decay hypotheses replaced by one Gaussian
    bound in `Im x` (valid for `|Im x| >= 1`). -/
theorem lineUp_eq_of_strip' {F : ℂ → ℂ} {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂)
    (hcont : ContinuousOn F {x : ℂ | x.re - x.im ∈ Icc c₁ c₂})
    (hdiff : DifferentiableOn ℂ F {x : ℂ | x.re - x.im ∈ Ioo c₁ c₂})
    {C a b : ℝ} (ha : 0 < a)
    (hbound : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → 1 ≤ |x.im| →
      ‖F x‖ ≤ C * Real.exp (-a * x.im ^ 2 + b * |x.im|)) :
    lineUp c₁ F = lineUp c₂ F := by
  refine lineUp_eq_of_strip hc hcont hdiff
    (integrable_lineUp ⟨le_rfl, hc⟩ hcont ha hbound)
    (integrable_lineUp ⟨hc, le_rfl⟩ hcont ha hbound) (fun ε hε => ?_)
  obtain ⟨Y, hY1, hY⟩ := gauss_tail_small (C := C) (b := b) ha ε hε
  refine ⟨2 * Y + (|c₁| + |c₂|), fun x hx hR => ?_⟩
  have hn := norm_le_of_upStrip hx
  have him : Y ≤ |x.im| := by linarith
  exact (hbound x hx (le_trans hY1 him)).trans (hY _ him)







/-! ## 5. Linearity and translation of line integrals -/













/-! ## 6. Holomorphy of the kernels off the integers -/

theorem rsD_ne_zero_of_ne {x : ℂ} (h : ∀ n : ℤ, x ≠ n) : rsD x ≠ 0 := by
  intro h0; obtain ⟨n, hn⟩ := (rsD_eq_zero_iff x).mp h0; exact h n hn











/-! ## 7. The Fresnel/Gaussian integrands are integrable along the lines -/









/-! ## 8. Moving the line inside a gap, and across a pole -/











/-! ## 9. The slope-(-1) side by conjugation -/

















/-! ## 10. The Mordell closed form -/



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



/-! ## 3. The amplitude near the saddle point -/







/-! ## 4. The saddle point is a global maximum along the steepest-descent line -/









/-! ## 4b. Integrability of the second Gaussian moment -/



/-! ## 5. The tau = 2 Mordell integral is uniformly bounded -/





theorem rsJ_line_eq {p : ℝ} {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂)
    (h₁ : -p < c₁) (h₂ : c₂ < 1 - p) (hc1 : -1 ≤ c₁) (hc2 : c₂ ≤ 1) :
    lineUp c₁ (fun w => cexp (2 * ↑π * I * w ^ 2) / rsD (p + w)) =
      lineUp c₂ (fun w => cexp (2 * ↑π * I * w ^ 2) / rsD (p + w)) := by
  have hD : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → rsD (p + x) ≠ 0 := by
    intro x hx
    refine rsD_ne_zero_of_ne fun n hn => ?_
    have him : x.im = 0 := by simpa using congrArg Complex.im hn
    have hre : p + x.re = n := by simpa using congrArg Complex.re hn
    rw [him, sub_zero] at hx
    have h1 : (0 : ℝ) < n := by linarith [hx.1]
    have h2 : (n : ℝ) < 1 := by linarith [hx.2]
    have h1' : (0 : ℤ) < n := by exact_mod_cast h1
    have h2' : n < (1 : ℤ) := by exact_mod_cast h2
    omega
  have hdA : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ →
      DifferentiableAt ℂ (fun w => cexp (2 * ↑π * I * w ^ 2) / rsD (p + w)) x := by
    intro x hx
    exact ((by fun_prop : Differentiable ℂ (fun w : ℂ => cexp (2 * ↑π * I * w ^ 2))) x).div
      ((differentiable_rsD.comp (by fun_prop : Differentiable ℂ (fun w : ℂ => (p : ℂ) + w))) x)
      (hD x hx)
  refine lineUp_eq_of_strip' hc (fun x hx => (hdA x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hdA x ⟨hx.1.le, hx.2.le⟩).differentiableWithinAt) (C := 1) (a := 4 * π)
    (b := 4 * π) (by positivity) (fun x hx h1 => ?_)
  have hD1 : 1 ≤ ‖rsD (p + x)‖ := one_le_norm_rsD (by simpa using h1)
  rw [norm_div, Complex.norm_exp]
  have hre : (2 * (π : ℂ) * I * x ^ 2).re = -(4 * π * x.re * x.im) := by
    simp [pow_two, mul_re, mul_im]; ring
  rw [hre, one_mul]
  refine (div_le_self (Real.exp_pos _).le hD1).trans (Real.exp_le_exp.mpr ?_)
  have hd : |x.re - x.im| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hbd : -((x.re - x.im) * x.im) ≤ |x.im| := by
    calc -((x.re - x.im) * x.im) ≤ |(x.re - x.im) * x.im| := neg_le_abs _
      _ = |x.re - x.im| * |x.im| := abs_mul _ _
      _ ≤ 1 * |x.im| := mul_le_mul_of_nonneg_right hd (abs_nonneg _)
      _ = |x.im| := one_mul _
  have key : -(4 * π * x.re * x.im) =
      -(4 * π) * x.im ^ 2 + 4 * π * (-((x.re - x.im) * x.im)) := by ring
  rw [key]
  have := mul_le_mul_of_nonneg_left hbd (by positivity : (0 : ℝ) ≤ 4 * π)
  linarith

/-- The tau = 2 Mordell integral may be computed on the midline through `1/2 - p`. -/
theorem rsJ_eq_mid {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    rsJ p = lineUp (1 / 2 - p) (fun w => cexp (2 * ↑π * I * w ^ 2) / rsD (p + w)) := by
  unfold rsJ
  rcases le_total p (1 / 2) with h | h
  · exact rsJ_line_eq (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · exact (rsJ_line_eq (c₁ := 1 / 2 - p) (c₂ := 0) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith)).symm



/-! ## 6. The error integral `rsE1` is `O(1/a)` -/

















/-! ## 7. The explicit C0 remainder bound -/













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

section
namespace RSInt
end RSInt
open RSInt

/-! ## 1. The second Gaussian moment -/





/-! ## 2. Lower bound for the denominator -/



/-! ## 3. The amplitude near the saddle point -/







/-! ## 4. The saddle point is a global maximum along the steepest-descent line -/









/-! ## 4b. Integrability of the second Gaussian moment -/



/-! ## 5. The tau = 2 Mordell integral is uniformly bounded -/










theorem solution {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : ‖rsJ p‖ ≤ 4 := by
  rw [rsJ_eq_mid hp hp1]
  unfold lineUp
  set c : ℝ := 1 / 2 - p with hc
  have hcb : c ^ 2 ≤ 1 / 4 := by
    have h1 : -(1 / 2) < c := by linarith
    have h2 : c < 1 / 2 := by linarith
    nlinarith
  have hbound : ∀ v : ℝ, ‖cexp (2 * ↑π * I * ((c : ℂ) + v * (1 + I)) ^ 2) /
      rsD (p + ((c : ℂ) + v * (1 + I))) * (1 + I)‖ ≤
      Real.sqrt 2 / 2 * Real.exp 2 * Real.exp (-(2 * π) * v ^ 2) := by
    intro v
    have hpt : (p : ℂ) + ((c : ℂ) + v * (1 + I)) = (1 / 2 : ℂ) + v * (1 + I) := by
      rw [hc]; push_cast; ring
    rw [hpt, norm_mul, norm_div, norm_one_add_I, Complex.norm_exp]
    have hre : (2 * (π : ℂ) * I * ((c : ℂ) + v * (1 + I)) ^ 2).re = -(4 * π * (c + v) * v) := by
      simp [pow_two, mul_re, mul_im]; ring
    rw [hre]
    have hD := two_le_norm_rsD_midline v
    have hexp : Real.exp (-(4 * π * (c + v) * v)) ≤ Real.exp 2 * Real.exp (-(2 * π) * v ^ 2) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
      have h0 : 0 ≤ 2 * π * (c + v) ^ 2 := by positivity
      have hpi : π ≤ 4 := by linarith [Real.pi_lt_d2]
      have h3 : 2 * π * c ^ 2 ≤ 2 := by nlinarith [Real.pi_pos]
      nlinarith
    calc Real.exp (-(4 * π * (c + v) * v)) / ‖rsD ((1 / 2 : ℂ) + v * (1 + I))‖ * Real.sqrt 2
        ≤ Real.exp 2 * Real.exp (-(2 * π) * v ^ 2) / 2 * Real.sqrt 2 := by
          gcongr
      _ = Real.sqrt 2 / 2 * Real.exp 2 * Real.exp (-(2 * π) * v ^ 2) := by ring
  have hint : Integrable (fun v : ℝ => Real.sqrt 2 / 2 * Real.exp 2 * Real.exp (-(2 * π) * v ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  refine le_trans (norm_integral_le_of_norm_le hint (Eventually.of_forall fun v => ?_)) ?_
  · exact hbound v
  · rw [integral_const_mul, integral_gaussian]
    have h1 : Real.sqrt (π / (2 * π)) = Real.sqrt (1 / 2) := by
      congr 1; field_simp
    have h2 : Real.sqrt 2 * Real.sqrt (1 / 2) = 1 := by
      rw [← Real.sqrt_mul (by norm_num)]; norm_num
    have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have he1 := Real.exp_one_lt_d9
    have he0 := Real.exp_pos 1
    rw [h1]
    calc Real.sqrt 2 / 2 * Real.exp 2 * Real.sqrt (1 / 2)
        = Real.exp 2 / 2 * (Real.sqrt 2 * Real.sqrt (1 / 2)) := by ring
      _ ≤ 4 := by rw [h2, he]; nlinarith

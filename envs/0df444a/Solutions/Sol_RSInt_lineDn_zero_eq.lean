-- Prove2me | solution 1 for RSInt.lineDn_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:13:35.375893+00:00
-- url     : https://prove2.me/submissions/e6450c6f-8530-4a60-9cb4-4c70eb262e52

import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_continuousAt_rsH_cpow_zero
import Theorems.Thm_RSInt_integrable_of_continuous_of_tail
import Theorems.Thm_RSInt_lineDn_eq_of_strip
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



















theorem norm_le_of_dnStrip {x : ℂ} {c₁ c₂ : ℝ} (hx : x.re + x.im ∈ Icc c₁ c₂) :
    ‖x‖ ≤ 2 * |x.im| + (|c₁| + |c₂|) := by
  have h1 := Complex.norm_le_abs_re_add_abs_im x
  have hd : |x.re + x.im| ≤ |c₁| + |c₂| := by
    rw [abs_le]; constructor
    · linarith [hx.1, neg_abs_le c₁, abs_nonneg c₂]
    · linarith [hx.2, le_abs_self c₂, abs_nonneg c₁]
  have h2 : |x.re| ≤ |x.im| + |x.re + x.im| := by
    calc |x.re| = |(-x.im) + (x.re + x.im)| := by ring_nf
      _ ≤ |-x.im| + |x.re + x.im| := abs_add_le _ _
      _ = |x.im| + |x.re + x.im| := by rw [abs_neg]
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







theorem lineDn_pt_im (c v : ℝ) : ((c : ℂ) + v * (1 - I)).im = -v := by simp



theorem integrable_lineDn {F : ℂ → ℂ} {c₁ c₂ c : ℝ} (hc : c ∈ Icc c₁ c₂)
    (hcont : ContinuousOn F {x : ℂ | x.re + x.im ∈ Icc c₁ c₂})
    {C a b : ℝ} (ha : 0 < a)
    (hbound : ∀ x : ℂ, x.re + x.im ∈ Icc c₁ c₂ → 1 ≤ |x.im| →
      ‖F x‖ ≤ C * Real.exp (-a * x.im ^ 2 + b * |x.im|)) :
    Integrable (fun v : ℝ => F (c + v * (1 - I))) := by
  have hmem : ∀ v : ℝ, ((c : ℂ) + v * (1 - I)) ∈ {x : ℂ | x.re + x.im ∈ Icc c₁ c₂} := by
    intro v
    simp only [mem_setOf_eq]
    have e : ((c : ℂ) + v * (1 - I)).re + ((c : ℂ) + v * (1 - I)).im = c := by simp
    rw [e]; exact hc
  refine integrable_of_continuous_of_tail (a := a) (b := b) (C := C) (R := 1)
    (hcont.comp_continuous (by fun_prop) hmem) ha (fun v hv => ?_)
  have := hbound _ (hmem v) (by rw [lineDn_pt_im, abs_neg]; exact hv)
  rwa [lineDn_pt_im, abs_neg, neg_sq] at this



theorem lineDn_eq_of_strip' {F : ℂ → ℂ} {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂)
    (hcont : ContinuousOn F {x : ℂ | x.re + x.im ∈ Icc c₁ c₂})
    (hdiff : DifferentiableOn ℂ F {x : ℂ | x.re + x.im ∈ Ioo c₁ c₂})
    {C a b : ℝ} (ha : 0 < a)
    (hbound : ∀ x : ℂ, x.re + x.im ∈ Icc c₁ c₂ → 1 ≤ |x.im| →
      ‖F x‖ ≤ C * Real.exp (-a * x.im ^ 2 + b * |x.im|)) :
    lineDn c₁ F = lineDn c₂ F := by
  refine lineDn_eq_of_strip hc hcont hdiff
    (integrable_lineDn ⟨le_rfl, hc⟩ hcont ha hbound)
    (integrable_lineDn ⟨hc, le_rfl⟩ hcont ha hbound) (fun ε hε => ?_)
  obtain ⟨Y, hY1, hY⟩ := gauss_tail_small (C := C) (b := b) ha ε hε
  refine ⟨2 * Y + (|c₁| + |c₂|), fun x hx hR => ?_⟩
  have hn := norm_le_of_dnStrip hx
  have him : Y ≤ |x.im| := by linarith
  exact (hbound x hx (le_trans hY1 him)).trans (hY _ him)





/-! ## 5. Linearity and translation of line integrals -/













/-! ## 6. Holomorphy of the kernels off the integers -/





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





/-! ## 3. Folding the line through 0 -/











theorem growth_cpow_sub_one {s : ℂ} (hs : 1 ≤ s.re) (x : ℂ) :
    ‖x ^ (s - 1)‖ ≤ Real.exp (π * |s.im|) * Real.exp ((s.re - 1) * ‖x‖) := by
  have := norm_cpow_le_exp (w := s - 1) (by simp; linarith) x
  simpa using this





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

















/-! ## 4. Moving the chi-side line off the pole -/


theorem solution {s : ℂ} (hs : 2 < s.re) {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    lineDn 0 (fun x => rsH x * x ^ (s - 1)) = lineDn c (fun x => rsH x * x ^ (s - 1)) := by
  -- the strip contains no integer other than 0, and meets the slit only at 0
  have hint0 : ∀ x : ℂ, x.re + x.im ∈ Icc (0 : ℝ) c → x ≠ 0 → rsD x ≠ 0 := by
    intro x hx hx0 h0
    obtain ⟨n, rfl⟩ := (rsD_eq_zero_iff x).mp h0
    have hn : (n : ℝ) ∈ Icc (0 : ℝ) c := by simpa using hx
    have h1 : 0 ≤ n := by exact_mod_cast hn.1
    have h2 : n < 1 := by exact_mod_cast (show (n : ℝ) < 1 by linarith [hn.2])
    have : n = 0 := by omega
    exact hx0 (by rw [this]; simp)
  have hslit : ∀ x : ℂ, x.re + x.im ∈ Icc (0 : ℝ) c → x ≠ 0 → x ∈ slitPlane := by
    intro x hx hx0
    rw [mem_slitPlane_iff]
    by_contra h
    rw [not_or, not_lt, not_not] at h
    have hre : x.re = 0 := by linarith [hx.1, h.1, h.2]
    exact hx0 (Complex.ext hre h.2)
  refine lineDn_eq_of_strip' hc.le ?_ ?_ (a := 2 * π) (by positivity)
    (C := |Real.exp (π * |s.im|)| * Real.exp (|s.re - 1| * (|(0 : ℝ)| + |c|)))
    (b := 2 * π * (|(0 : ℝ)| + |c|) + 2 * |s.re - 1|)
    (fun x hx h1 => norm_rsH_mul_le (ψ := fun x => x ^ (s - 1)) hx h1
      (growth_cpow_sub_one (by linarith) _))
  · intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact (continuousAt_rsH_cpow_zero hs).continuousWithinAt
    · exact ((differentiableAt_rsH (hint0 x hx hx0)).continuousAt.mul
        (continuousAt_cpow_const (hslit x hx hx0))).continuousWithinAt
  · intro x hx
    have hx' : x.re + x.im ∈ Icc (0 : ℝ) c := ⟨hx.1.le, hx.2.le⟩
    have hx0 : x ≠ 0 := by intro h; rw [h] at hx; simp at hx
    exact ((differentiableAt_rsH (hint0 x hx' hx0)).mul
      ((differentiableAt_id).cpow (differentiableAt_const _) (hslit x hx' hx0))).differentiableWithinAt

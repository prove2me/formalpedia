-- Prove2me | solution 1 for RSInt.lineUp_rsG_jump
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:14:17.80352+00:00
-- url     : https://prove2.me/submissions/6cb852c8-15a3-4510-9dd8-24ba19437664

import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_integrable_lineUp_rsG_mul
import Theorems.Thm_RSInt_integrable_of_continuous_of_tail
import Theorems.Thm_RSInt_lineUp_eq_of_strip
import Theorems.Thm_RSInt_lineUp_gauss
import Theorems.Thm_RSInt_norm_rsG_mul_le
import Theorems.Thm_RSInt_rsG_add_one
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







theorem pi_ne_zero' : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero

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

theorem one_add_I_sq : (1 + I : ℂ) ^ 2 = 2 * I := by
  ring_nf; rw [I_sq]; ring







theorem lineUp_gauss_zero (c : ℝ) :
    lineUp c (fun x => cexp (↑π * I * (x ^ 2 + x))) = 1 := by
  have := lineUp_gauss c 0
  simp only [mul_zero, sub_zero, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero, Complex.exp_zero] at this
  exact this

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

theorem lineUp_congr {F G : ℂ → ℂ} {c : ℝ}
    (h : ∀ v : ℝ, F (c + v * (1 + I)) = G (c + v * (1 + I))) : lineUp c F = lineUp c G := by
  unfold lineUp; congr 1; ext v; rw [h]





theorem lineUp_add {F G : ℂ → ℂ} {c : ℝ}
    (hF : Integrable (fun v : ℝ => F (c + v * (1 + I))))
    (hG : Integrable (fun v : ℝ => G (c + v * (1 + I)))) :
    lineUp c (fun x => F x + G x) = lineUp c F + lineUp c G := by
  unfold lineUp
  rw [← integral_add (hF.mul_const _) (hG.mul_const _)]
  congr 1; ext v; ring



theorem lineUp_add_one (c : ℝ) (F : ℂ → ℂ) :
    lineUp (c + 1) F = lineUp c (fun x => F (x + 1)) := by
  unfold lineUp; congr 1; ext v; congr 2; push_cast; ring

/-! ## 6. Holomorphy of the kernels off the integers -/

theorem rsD_ne_zero_of_ne {x : ℂ} (h : ∀ n : ℤ, x ≠ n) : rsD x ≠ 0 := by
  intro h0; obtain ⟨n, hn⟩ := (rsD_eq_zero_iff x).mp h0; exact h n hn

theorem differentiableAt_rsG {x : ℂ} (h : rsD x ≠ 0) : DifferentiableAt ℂ rsG x := by
  unfold rsG
  exact ((by fun_prop : Differentiable ℂ (fun x : ℂ => cexp (↑π * I * x ^ 2))) x).div
    (differentiable_rsD x) h



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

theorem fresnel_pt (c : ℝ) (B : ℂ) (v : ℝ) :
    cexp (↑π * I * ((c : ℂ) + v * (1 + I) + B) ^ 2) =
      cexp ((-2 * ↑π) * (v : ℂ) ^ 2 + (2 * ↑π * I * (c + B) * (1 + I)) * v + ↑π * I * (c + B) ^ 2) := by
  congr 1
  linear_combination (↑π * I * (v : ℂ) ^ 2) * one_add_I_sq + (2 * ↑π * (v : ℂ) ^ 2) * I_sq

theorem integrable_fresnel (c : ℝ) (B : ℂ) :
    Integrable (fun v : ℝ => cexp (↑π * I * ((c : ℂ) + v * (1 + I) + B) ^ 2)) := by
  have := integrable_cexp_quadratic' (b := -2 * ↑π) (by simp [Real.pi_pos])
    (2 * ↑π * I * (c + B) * (1 + I)) (↑π * I * (c + B) ^ 2)
  refine this.congr (Eventually.of_forall fun v => ?_)
  beta_reduce
  rw [fresnel_pt]

theorem gauss_pt (y x : ℂ) :
    cexp (↑π * I * (x ^ 2 + x) - x * y) =
      cexp (↑π * I * (x + (1 / 2 + I * y / (2 * ↑π))) ^ 2) *
        cexp (-(↑π * I * (1 / 2 + I * y / (2 * ↑π)) ^ 2)) := by
  rw [← Complex.exp_add]
  congr 1
  have hpi := pi_ne_zero'
  field_simp
  linear_combination (-(4 * ↑π * x * y)) * I_sq

theorem integrable_lineUp_gauss (c : ℝ) (y : ℂ) :
    Integrable (fun v : ℝ => cexp (↑π * I * (((c : ℂ) + v * (1 + I)) ^ 2 + ((c : ℂ) + v * (1 + I)))
      - ((c : ℂ) + v * (1 + I)) * y)) := by
  have := (integrable_fresnel c (1 / 2 + I * y / (2 * ↑π))).mul_const
    (cexp (-(↑π * I * (1 / 2 + I * y / (2 * ↑π)) ^ 2)))
  refine this.congr (Eventually.of_forall fun v => ?_)
  beta_reduce
  rw [gauss_pt]

/-! ## 8. Moving the line inside a gap, and across a pole -/

/-- **Same gap.**  If the closed crossing interval `[c1, c2]` contains no integer, the slope-(+1)
    integral of `rsG * phi` does not depend on the crossing point. -/
theorem lineUp_same_gap {φ : ℂ → ℂ} {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂)
    (hno : ∀ m : ℤ, (m : ℝ) ∉ Icc c₁ c₂)
    (hφ : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → DifferentiableAt ℂ φ x)
    {A B : ℝ} (hgrow : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → ‖φ x‖ ≤ A * Real.exp (B * ‖x‖)) :
    lineUp c₁ (fun x => rsG x * φ x) = lineUp c₂ (fun x => rsG x * φ x) := by
  have hD : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → rsD x ≠ 0 := by
    intro x hx
    refine rsD_ne_zero_of_ne fun n hn => hno n ?_
    rw [hn] at hx; simpa using hx
  have hdA : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → DifferentiableAt ℂ (fun x => rsG x * φ x) x :=
    fun x hx => (differentiableAt_rsG (hD x hx)).mul (hφ x hx)
  exact lineUp_eq_of_strip' hc (fun x hx => (hdA x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hdA x ⟨hx.1.le, hx.2.le⟩).differentiableWithinAt) (a := 2 * π)
    (by positivity) (fun x hx h1 => norm_rsG_mul_le hx h1 (hgrow x hx))



theorem integrable_lineUp_rsG {c : ℝ} (hcl : ∀ m : ℤ, (m : ℝ) ≠ c) :
    Integrable (fun v : ℝ => rsG (c + v * (1 + I))) := by
  have := integrable_lineUp_rsG_mul (φ := fun _ => (1 : ℂ)) (c₁ := c) (c₂ := c) ⟨le_rfl, le_rfl⟩
    hcl (fun x _ => continuousAt_const) (A := 1) (B := 0) (fun x _ => by simp)
  simpa using this





/-! ## 9. The slope-(-1) side by conjugation -/

















/-! ## 10. The Mordell closed form -/



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

section
namespace RSInt
end RSInt
open RSInt

/-! ## 1. The kernels and their algebra -/



























/-! ## 2. Norm bounds -/

























/-! ## 3. The Fresnel line integral -/











/-! ## 4. Gaussian tails, line integrability, and the strip wrappers -/























/-! ## 5. Linearity and translation of line integrals -/













/-! ## 6. Holomorphy of the kernels off the integers -/













/-! ## 7. The Fresnel/Gaussian integrands are integrable along the lines -/









/-! ## 8. Moving the line inside a gap, and across a pole -/








theorem solution {n : ℤ} {c₁ c₂ : ℝ}
    (h₁ : (n : ℝ) - 1 < c₁) (h₁' : c₁ < n) (h₂ : (n : ℝ) < c₂) (h₂' : c₂ < n + 1) :
    lineUp c₂ rsG = lineUp c₁ rsG + 1 := by
  have hcl₁ : ∀ m : ℤ, (m : ℝ) ≠ c₁ :=
    notInt_of_Ioo (n := n - 1) (by push_cast; linarith) (by push_cast; linarith)
  have hstep : lineUp (c₁ + 1) rsG = lineUp c₁ rsG + 1 := by
    rw [lineUp_add_one]
    have h1 : lineUp c₁ (fun x => rsG (x + 1)) =
        lineUp c₁ (fun x => rsG x + cexp (↑π * I * (x ^ 2 + x))) := by
      refine lineUp_congr fun v => ?_
      exact rsG_add_one _ (rsD_ne_zero_of_ne (lineUp_pt_ne_int hcl₁ v))
    have hg : Integrable (fun v : ℝ => cexp (↑π * I * (((c₁ : ℂ) + v * (1 + I)) ^ 2 +
        ((c₁ : ℂ) + v * (1 + I))))) := by
      simpa using integrable_lineUp_gauss c₁ 0
    rw [h1, lineUp_add (integrable_lineUp_rsG hcl₁) hg, lineUp_gauss_zero]
  have hmid : lineUp c₂ rsG = lineUp (c₁ + 1) rsG := by
    have hno : ∀ c c' : ℝ, c ≤ c' → (n : ℝ) < c → c' < n + 1 →
        lineUp c rsG = lineUp c' rsG := by
      intro c c' hcc hc hc'
      have := lineUp_same_gap (φ := fun _ => (1 : ℂ)) hcc
        (fun m hm => notInt_of_Ioo (n := n) (lt_of_lt_of_le hc hm.1) (lt_of_le_of_lt hm.2 hc') m
          rfl) (fun x _ => differentiableAt_const _) (A := 1) (B := 0) (fun x _ => by simp)
      simpa using this
    rcases le_total c₂ (c₁ + 1) with h | h
    · exact hno _ _ h h₂ (by linarith)
    · exact (hno _ _ h (by linarith) h₂').symm
  rw [hmid, hstep]

-- Prove2me | solution 1 for RSInt.lineUp_eq_of_strip
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:11:51.349003+00:00
-- url     : https://prove2.me/submissions/db3ba9fe-48fd-47be-9f36-bea25cd9875a

import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_strip_integral_eq
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





theorem lineUp_point (c u : ℝ) :
    (c : ℂ) + ((u - c / 2 : ℝ) : ℂ) * (1 + I) = (1 + I) * ((u : ℂ) + ((-c / 2 : ℝ) : ℂ) * I) := by
  push_cast; ring_nf; rw [I_sq]; ring



/-- `lineUp` as a horizontal-line integral in the rotated coordinate `z`, `x = (1 + I) z`. -/
theorem lineUp_eq_rot (c : ℝ) (F : ℂ → ℂ) :
    lineUp c F = ∫ u : ℝ, F ((1 + I) * ((u : ℂ) + ((-c / 2 : ℝ) : ℂ) * I)) * (1 + I) := by
  unfold lineUp
  rw [← integral_sub_right_eq_self (fun v : ℝ => F (c + v * (1 + I)) * (1 + I)) (c / 2)]
  congr 1
  ext u
  rw [lineUp_point]



theorem re_sub_im_rotUp (z : ℂ) : ((1 + I) * z).re - ((1 + I) * z).im = -2 * z.im := by
  simp [mul_re, mul_im]; ring



theorem norm_rot_ge (w z : ℂ) (hw : ‖w‖ = Real.sqrt 2) : |z.re| ≤ ‖w * z‖ := by
  rw [norm_mul, hw]
  have h1 : |z.re| ≤ ‖z‖ := abs_re_le_norm z
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  nlinarith [norm_nonneg z]

theorem norm_one_add_I : ‖(1 + I : ℂ)‖ = Real.sqrt 2 := by
  rw [Complex.norm_def, Complex.normSq_apply]; simp; norm_num







end RSInt

end

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

section
namespace RSInt
end RSInt
open RSInt

/-! ## 1. Integrability from a Gaussian tail -/







/-! ## 2. Cauchy's theorem on a horizontal strip -/



/-! ## 3. Slanted lines -/
























theorem solution {F : ℂ → ℂ} {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂)
    (hcont : ContinuousOn F {x : ℂ | x.re - x.im ∈ Icc c₁ c₂})
    (hdiff : DifferentiableOn ℂ F {x : ℂ | x.re - x.im ∈ Ioo c₁ c₂})
    (hint₁ : Integrable (fun v : ℝ => F (c₁ + v * (1 + I))))
    (hint₂ : Integrable (fun v : ℝ => F (c₂ + v * (1 + I))))
    (hdecay : ∀ ε > 0, ∃ R : ℝ, ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → R ≤ ‖x‖ → ‖F x‖ ≤ ε) :
    lineUp c₁ F = lineUp c₂ F := by
  rw [lineUp_eq_rot, lineUp_eq_rot]
  set f : ℂ → ℂ := fun z => F ((1 + I) * z) * (1 + I) with hf
  have hy : -c₂ / 2 ≤ -c₁ / 2 := by linarith
  have hmaps : ∀ z : ℂ, z.im ∈ Icc (-c₂ / 2) (-c₁ / 2) →
      ((1 + I) * z).re - ((1 + I) * z).im ∈ Icc c₁ c₂ := by
    intro z hz
    rw [re_sub_im_rotUp]
    exact ⟨by linarith [hz.2], by linarith [hz.1]⟩
  have hmapso : ∀ z : ℂ, z.im ∈ Ioo (-c₂ / 2) (-c₁ / 2) →
      ((1 + I) * z).re - ((1 + I) * z).im ∈ Ioo c₁ c₂ := by
    intro z hz
    rw [re_sub_im_rotUp]
    exact ⟨by linarith [hz.2], by linarith [hz.1]⟩
  have key := strip_integral_eq (f := f) hy
    (by
      intro z hz
      exact ((hcont _ (hmaps z hz)).comp (continuousWithinAt_id.const_mul (1 + I))
        (fun w hw => hmaps w hw)).mul continuousWithinAt_const)
    (by
      intro z hz
      exact ((hdiff _ (hmapso z hz)).comp z ((differentiableWithinAt_id).const_mul (1 + I))
        (fun w hw => hmapso w hw)).mul (differentiableWithinAt_const _))
    (by
      have := (hint₂.comp_sub_right (c₂ / 2)).mul_const (1 + I)
      refine this.congr (Eventually.of_forall fun u => ?_)
      simp only [hf]
      rw [lineUp_point])
    (by
      have := (hint₁.comp_sub_right (c₁ / 2)).mul_const (1 + I)
      refine this.congr (Eventually.of_forall fun u => ?_)
      simp only [hf]
      rw [lineUp_point])
    (by
      intro ε hε
      obtain ⟨R, hR⟩ := hdecay (ε / Real.sqrt 2) (by positivity)
      refine ⟨R, fun x y hx hy' => ?_⟩
      have hm := hmaps (x + y * I) (by simpa using hy')
      have hnorm : R ≤ ‖(1 + I) * ((x : ℂ) + y * I)‖ := by
        have h := norm_rot_ge (1 + I) ((x : ℂ) + y * I) norm_one_add_I
        have hre : ((x : ℂ) + y * I).re = x := by simp
        rw [hre] at h
        linarith
      simp only [hf]
      rw [norm_mul, norm_one_add_I]
      have := hR _ hm hnorm
      calc ‖F ((1 + I) * (↑x + ↑y * I))‖ * Real.sqrt 2 ≤ ε / Real.sqrt 2 * Real.sqrt 2 :=
            mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg 2)
        _ = ε := by field_simp)
  simp only [hf] at key
  exact key.symm

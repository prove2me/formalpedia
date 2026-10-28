-- Prove2me | solution 1 for RSInt.integrable_of_continuous_of_tail
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:53:05.838317+00:00
-- url     : https://prove2.me/submissions/f93773a0-9de7-4e89-b7d8-15d8c72aa91a

import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
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

theorem integrable_exp_quad {a b : ℝ} (ha : 0 < a) :
    Integrable (fun v : ℝ => Real.exp (-a * v ^ 2 + b * |v|)) := by
  have h1 : Integrable (fun v : ℝ => Real.exp (b ^ 2 / (2 * a)) * Real.exp (-(a / 2) * v ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  refine h1.mono' (by fun_prop) (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_quad_le a b v ha



/-! ## 2. Cauchy's theorem on a horizontal strip -/



/-! ## 3. Slanted lines -/



























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






theorem solution {f : ℝ → ℂ} (hf : Continuous f) {a b C R : ℝ}
    (ha : 0 < a) (htail : ∀ v : ℝ, R ≤ |v| → ‖f v‖ ≤ C * Real.exp (-a * v ^ 2 + b * |v|)) :
    Integrable f := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hf.continuousOn
  have hind : Integrable (Set.indicator (Icc (-R) R) (fun _ : ℝ => M)) :=
    (integrableOn_const (C := M) (by simp)).integrable_indicator measurableSet_Icc
  have hint : Integrable (fun v : ℝ =>
      Set.indicator (Icc (-R) R) (fun _ : ℝ => M) v + |C| * Real.exp (-a * v ^ 2 + b * |v|)) :=
    hind.add ((integrable_exp_quad ha).const_mul _)
  refine hint.mono' hf.aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  have hE : 0 ≤ |C| * Real.exp (-a * v ^ 2 + b * |v|) := by positivity
  by_cases hv : v ∈ Icc (-R) R
  · rw [Set.indicator_of_mem hv]
    have := hM v hv
    linarith
  · rw [Set.indicator_of_notMem hv, zero_add]
    have hRv : R ≤ |v| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hv
      rcases hv with hv | hv
      · linarith [neg_le_abs v]
      · linarith [le_abs_self v]
    calc ‖f v‖ ≤ C * Real.exp (-a * v ^ 2 + b * |v|) := htail v hRv
      _ ≤ |C| * Real.exp (-a * v ^ 2 + b * |v|) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le

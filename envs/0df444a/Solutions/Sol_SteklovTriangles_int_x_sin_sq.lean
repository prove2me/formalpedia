-- Prove2me | solution 1 for SteklovTriangles.int_x_sin_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:58:11.929416+00:00
-- url     : https://prove2.me/submissions/8b058c8a-f413-43c1-b214-439bfad6c14c

import Mathlib
import Definitions.Def_SteklovTriangles_CosBound

set_option autoImplicit false
open SteklovTriangles
open Real intervalIntegral
namespace SteklovTriangles
theorem _root_.solution (p : ℝ) :
    ∫ x in (0:ℝ)..p, x * sin (π * x) ^ 2
      = p ^ 2 / 4 - p * sin (2 * π * p) / (4 * π) - (cos (2 * π * p) - 1) / (8 * π ^ 2) := by
  have hπ : π ≠ 0 := pi_ne_zero
  let F : ℝ → ℝ := fun x => x ^ 2 / 4 - x * sin (2 * π * x) / (4 * π) - cos (2 * π * x) / (8 * π ^ 2)
  have hF : ∀ x ∈ Set.uIcc (0:ℝ) p, HasDerivAt F (x * sin (π * x) ^ 2) x := by
    intro x _
    have h2 : HasDerivAt (fun x : ℝ => 2 * π * x) (2 * π) x := by
      simpa using (hasDerivAt_id x).const_mul (2 * π)
    have hs := h2.sin
    have hc := h2.cos
    have hx2 : HasDerivAt (fun x : ℝ => x ^ 2 / 4) (2 * x / 4) x := by
      simpa using (hasDerivAt_pow 2 x).div_const 4
    have hxs : HasDerivAt (fun x : ℝ => x * sin (2 * π * x) / (4 * π))
        ((1 * sin (2 * π * x) + x * (cos (2 * π * x) * (2 * π))) / (4 * π)) x :=
      ((hasDerivAt_id x).mul hs).div_const (4 * π)
    have hcc : HasDerivAt (fun x : ℝ => cos (2 * π * x) / (8 * π ^ 2))
        ((-sin (2 * π * x) * (2 * π)) / (8 * π ^ 2)) x := hc.div_const (8 * π ^ 2)
    have h1 := (hx2.sub hxs).sub hcc
    have hcos : cos (2 * π * x) = 1 - 2 * sin (π * x) ^ 2 := by
      rw [show 2 * π * x = 2 * (π * x) by ring, cos_two_mul, cos_sq']; ring
    have hderiv : 2 * x / 4 - (1 * sin (2 * π * x) + x * (cos (2 * π * x) * (2 * π))) / (4 * π) -
        -sin (2 * π * x) * (2 * π) / (8 * π ^ 2) = x * sin (π * x) ^ 2 := by
      rw [hcos]; field_simp; ring
    rw [hderiv] at h1
    exact h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by simp [F, Pi.sub_apply])
  have hint : IntervalIntegrable (fun x : ℝ => x * sin (π * x) ^ 2) MeasureTheory.volume 0 p :=
    (by fun_prop : Continuous (fun x : ℝ => x * sin (π * x) ^ 2)).intervalIntegrable 0 p
  rw [integral_eq_sub_of_hasDerivAt hF hint]
  simp only [F]
  simp
  ring
end SteklovTriangles

-- Prove2me | solution 1 for SteklovTriangles.int_cos_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:58:22.506062+00:00
-- url     : https://prove2.me/submissions/2265ffe9-0951-47b4-984e-e711621b8735

import Mathlib
import Definitions.Def_SteklovTriangles_CosBound

set_option autoImplicit false
open SteklovTriangles
open Real intervalIntegral
namespace SteklovTriangles
theorem _root_.solution (p : ℝ) :
    ∫ x in (0:ℝ)..p, cos (π * x) ^ 2 = p / 2 + sin (2 * π * p) / (4 * π) := by
  have hπ : π ≠ 0 := pi_ne_zero
  let F : ℝ → ℝ := fun x => x / 2 + sin (2 * π * x) / (4 * π)
  have hF : ∀ x ∈ Set.uIcc (0:ℝ) p, HasDerivAt F (cos (π * x) ^ 2) x := by
    intro x _
    have h2 : HasDerivAt (fun x : ℝ => 2 * π * x) (2 * π) x := by
      simpa using (hasDerivAt_id x).const_mul (2 * π)
    have h1 := ((hasDerivAt_id x).div_const 2).add (h2.sin.div_const (4 * π))
    have hcos : cos (2 * π * x) = 2 * cos (π * x) ^ 2 - 1 := by
      rw [show 2 * π * x = 2 * (π * x) by ring, cos_two_mul]
    have hderiv : 1 / 2 + cos (2 * π * x) * (2 * π) / (4 * π) = cos (π * x) ^ 2 := by
      rw [hcos]; field_simp; ring
    rw [hderiv] at h1
    exact h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by simp [F, Pi.add_apply])
  have hint : IntervalIntegrable (fun x : ℝ => cos (π * x) ^ 2) MeasureTheory.volume 0 p :=
    (by fun_prop : Continuous (fun x : ℝ => cos (π * x) ^ 2)).intervalIntegrable 0 p
  rw [integral_eq_sub_of_hasDerivAt hF hint]
  simp [F]
end SteklovTriangles

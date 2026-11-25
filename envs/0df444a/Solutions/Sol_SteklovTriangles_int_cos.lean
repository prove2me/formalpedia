-- Prove2me | solution 1 for SteklovTriangles.int_cos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:58:24.091714+00:00
-- url     : https://prove2.me/submissions/55875271-e1f8-4d84-9121-8706cb778ace

import Mathlib
import Definitions.Def_SteklovTriangles_CosBound

set_option autoImplicit false
open SteklovTriangles
open Real intervalIntegral
namespace SteklovTriangles
theorem _root_.solution (p : ℝ) : ∫ x in (0:ℝ)..p, cos (π * x) = sin (π * p) / π := by
  have hπ : π ≠ 0 := pi_ne_zero
  have := integral_comp_mul_left (fun x => cos x) hπ (a := 0) (b := p)
  simp only [mul_zero] at this
  rw [this, integral_cos]
  simp
  field_simp
end SteklovTriangles

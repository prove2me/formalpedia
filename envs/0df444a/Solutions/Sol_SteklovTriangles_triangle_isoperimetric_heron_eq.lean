-- Prove2me | solution 1 for SteklovTriangles.triangle_isoperimetric_heron_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:52:42.784922+00:00
-- url     : https://prove2.me/submissions/6b623cdd-673b-44ba-97ba-795bd94f17fe

import Mathlib
import Definitions.Def_SteklovTriangles_AreaCorollary
import Theorems.Thm_SteklovTriangles_amgm3_eq

set_option autoImplicit false
open SteklovTriangles
namespace SteklovTriangles
theorem _root_.solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a < b + c) (h2 : b < a + c) (h3 : c < a + b)
    (heq : 27 * ((a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c)) = (a + b + c) ^ 4) :
    a = b ∧ b = c := by
  have hx : 0 ≤ -a + b + c := by linarith
  have hy : 0 ≤ a - b + c := by linarith
  have hz : 0 ≤ a + b - c := by linarith
  have hL : 0 < a + b + c := by linarith
  have hs : (-a + b + c) + (a - b + c) + (a + b - c) = a + b + c := by ring
  have h' : 27 * ((-a + b + c) * (a - b + c) * (a + b - c)) = ((-a + b + c) + (a - b + c) + (a + b - c)) ^ 3 := by
    rw [hs]
    have : (a + b + c) * (27 * ((-a + b + c) * (a - b + c) * (a + b - c))) = (a + b + c) * (a + b + c) ^ 3 := by
      rw [← mul_assoc]; nlinarith [heq]
    exact mul_left_cancel₀ (ne_of_gt hL) this
  obtain ⟨e1, e2⟩ := amgm3_eq _ _ _ hx hy hz h'
  constructor <;> linarith
end SteklovTriangles

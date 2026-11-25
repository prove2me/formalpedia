-- Prove2me | solution 1 for Research.sqDist_triPoint_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:17:09.900254+00:00
-- url     : https://prove2.me/submissions/eb1da5aa-ea4d-48e3-9f83-ae8f159420b8

module
public import Definitions.Def_Research_Basic
public import Definitions.Def_Research_TriangularShells

set_option autoImplicit true
@[expose] public section
public section
open Research
namespace Research
theorem _root_.solution (p : ℤ × ℤ) :
    sqDist (triPoint p) (0, 0) = (triNormSq p : ℝ) := by
  rcases p with ⟨a, b⟩
  simp only [triPoint, sqDist, triNormSq, sub_zero]
  have hs : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by norm_num
  rw [div_pow, mul_pow, hs]
  norm_num
  ring
end Research

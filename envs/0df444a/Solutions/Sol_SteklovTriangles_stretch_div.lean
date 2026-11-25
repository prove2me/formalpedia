-- Prove2me | solution 1 for SteklovTriangles.stretch_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:50:33.1503+00:00
-- url     : https://prove2.me/submissions/02208048-972b-426f-a628-6700ab0dffc9

import Mathlib
import Definitions.Def_SteklovTriangles_Reformulation

set_option autoImplicit false
open SteklovTriangles
namespace SteklovTriangles
theorem _root_.solution (s ρ κ : ℝ) (hs : 0 ≤ s) (hρ : ρ ≠ 0) (h : s ^ 2 = 1 + ρ * κ + ρ ^ 2) :
    (s - 1) / ρ = (κ + ρ) / (1 + s) := by
  have h1 : 1 + s ≠ 0 := by linarith
  rw [div_eq_div_iff hρ h1]
  nlinarith [h]
end SteklovTriangles

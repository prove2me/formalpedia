-- Prove2me | solution 1 for SteklovTriangles.G_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:50:30.287637+00:00
-- url     : https://prove2.me/submissions/3e4982e9-eb25-404e-ae94-26941652c10f

import Mathlib
import Definitions.Def_SteklovTriangles_Reformulation

set_option autoImplicit false
open SteklovTriangles
namespace SteklovTriangles
theorem _root_.solution (ρ a b : ℝ) (hd : 1 + ρ * b ≠ 0) :
    let d := 1 + ρ * b
    let G11 := 1 + ρ ^ 2 * a ^ 2 / d ^ 2
    let G12 := -(ρ * a) / d ^ 2
    let G22 := 1 / d ^ 2
    -- AᵀA = [[1, ρ a], [ρ a, ρ²a² + d²]]
    (1 * G11 + (ρ * a) * G12 = 1) ∧ (1 * G12 + (ρ * a) * G22 = 0) ∧
    ((ρ * a) * G11 + (ρ ^ 2 * a ^ 2 + d ^ 2) * G12 = 0) ∧
    ((ρ * a) * G12 + (ρ ^ 2 * a ^ 2 + d ^ 2) * G22 = 1) := by
  intro d G11 G12 G22
  have hd' : d ≠ 0 := hd
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp only [G11, G12, G22]; field_simp; ring)
end SteklovTriangles

-- Prove2me | solution 1 for Verlinde2016.density_parameter_relation
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:51:30.353986+00:00
-- url     : https://prove2.me/submissions/04c6be4a-ab92-40e4-80ed-e08091473d07

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
set_option autoImplicit false
open Real

theorem solution (G c H₀ ρ_B ρ_D : ℝ) (hG : 0 < G) (hc : 0 < c) (hH₀ : 0 < H₀)
    (h747 : ρ_D ^ 2 = (4 - 0) * (c * H₀) * ρ_B / (8 * π * G * (c / H₀))) :
    (ρ_D / (3 * H₀ ^ 2 / (8 * π * G))) ^ 2 = 4 / 3 * (ρ_B / (3 * H₀ ^ 2 / (8 * π * G))) := by
  have hpi := Real.pi_pos
  field_simp at h747 ⊢
  nlinarith [h747]

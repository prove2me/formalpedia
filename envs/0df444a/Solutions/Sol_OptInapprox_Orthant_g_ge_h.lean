-- Prove2me | solution 1 for OptInapprox.Orthant.g_ge_h
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:17:49.29897+00:00
-- url     : https://prove2.me/submissions/849672e0-5813-4dfc-b8c2-bd78f82683a2

import Mathlib
import Definitions.Def_OptInapprox_Orthant_Setting
set_option autoImplicit false
open MeasureTheory ProbabilityTheory OptInapprox.Orthant

theorem solution (t ρ u v : ℝ) (ht : 0 < t) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    hExp ρ t u v ≤ gExp ρ t u v := by
  unfold hExp gExp
  have h1 : 0 < 1 - ρ := by linarith
  have h2 : 0 < 1 - ρ ^ 2 := by nlinarith
  rw [add_div ((u - v) ^ 2)]
  have : 0 ≤ 2 * (1 - ρ) * u * v / (2 * (1 - ρ ^ 2) * t ^ 2) := by positivity
  linarith


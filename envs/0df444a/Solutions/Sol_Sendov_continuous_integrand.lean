-- Prove2me | solution 1 for Sendov.continuous_integrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:55:00.506376+00:00
-- url     : https://prove2.me/submissions/cc70e142-0e77-4ac3-8a0e-c48fa173b255

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_Common_Rpow
import Theorems.Thm_Sendov_continuous_rpow_const

set_option autoImplicit false
open Sendov
open MeasureTheory
namespace Sendov
theorem _root_.solution (n : ℕ) (α : ℝ) {e : ℝ} (he : 0 ≤ e) :
    Continuous fun t : ℝ => t ^ 3 * Q n α t ^ e := by
  have hQ : Continuous fun t : ℝ => Q n α t := by
    simp only [Q]; fun_prop
  have h3 : Continuous fun t : ℝ => t ^ 3 := by fun_prop
  exact h3.mul ((continuous_rpow_const he).comp hQ)
end Sendov

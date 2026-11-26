-- Prove2me | solution 1 for Sendov.log_le_div_exp_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:00:52.062808+00:00
-- url     : https://prove2.me/submissions/876c3974-c8cd-46cf-80a9-4286ba86e0b4

import Definitions.Def_Sendov_Reduction_Simplified
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_Sendov_Reduction_Alpha17

set_option autoImplicit false
open Sendov
open MeasureTheory Real
namespace Sendov
theorem _root_.solution {t : ℝ} (ht : 0 < t) : Real.log t ≤ t / exp 1 := by
  have h := Real.log_le_sub_one_of_pos (x := t / exp 1) (by positivity)
  rw [Real.log_div ht.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
  linarith
end Sendov

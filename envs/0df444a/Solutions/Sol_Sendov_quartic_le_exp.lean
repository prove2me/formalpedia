-- Prove2me | solution 1 for Sendov.quartic_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:00:49.109597+00:00
-- url     : https://prove2.me/submissions/66614af5-1587-40bb-a458-0b1b6cc25dba

import Definitions.Def_Sendov_Reduction_Simplified
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_Sendov_Reduction_Alpha17

set_option autoImplicit false
open Sendov
open MeasureTheory Real
namespace Sendov
theorem _root_.solution {z : ℝ} (hz : 0 ≤ z) : 1 + z + z ^ 2 / 2 + z ^ 3 / 6 ≤ exp z := by
  have h := Real.sum_le_exp_of_nonneg hz 4
  simp [Finset.sum_range_succ, Nat.factorial] at h
  linarith
end Sendov

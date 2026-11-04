-- Prove2me | solution 1 for Real.rpow_inv_le_natCast_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:04:17.783464+00:00
-- url     : https://prove2.me/submissions/1a7eb8e9-cdba-4195-82fb-9bdcf37fafa4

import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Ceil

set_option autoImplicit false
section
open Real
namespace Real
theorem _root_.solution {e : ℕ} (he : e ≠ 0) (x t : ℕ) :
    (t : ℝ) ^ ((e : ℝ)⁻¹) ≤ (x : ℝ) ↔ t ≤ x ^ e := by
  rw [Real.rpow_inv_le_iff_of_pos t.cast_nonneg x.cast_nonneg
    (Nat.cast_pos.2 (Nat.pos_of_ne_zero he)), Real.rpow_natCast]
  exact_mod_cast Iff.rfl
end Real

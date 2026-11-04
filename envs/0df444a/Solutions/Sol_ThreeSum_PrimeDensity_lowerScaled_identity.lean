-- Prove2me | solution 1 for ThreeSum.PrimeDensity.lowerScaled_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:43:58.954193+00:00
-- url     : https://prove2.me/submissions/2cb326e7-07a2-497d-9b52-d61f27f7c8e4

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Submission_ThreeSum_PrimeDensity

set_option autoImplicit false
open ThreeSum ThreeSum.PrimeDensity
open Real Filter Finset
open scoped Topology
noncomputable section
namespace ThreeSum.PrimeDensity
theorem _root_.solution {y : ℕ} (hy : 1 < y) :
    lowerScaled y * ((y : ℝ) / Real.log y) =
      ((4 * y : ℝ) * Real.log 2 - Real.log (4 * y + 1 : ℝ)) / Real.log (4 * y : ℝ) := by
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (lt_trans Nat.zero_lt_one hy)
  have hlog : (0 : ℝ) < Real.log y := Real.log_pos (by exact_mod_cast hy)
  have hlog4y : Real.log (4 * y : ℝ) = Real.log 4 + Real.log y :=
    Real.log_mul (by norm_num) hy0.ne'
  have hsum : Real.log 4 + Real.log y ≠ 0 := by
    have h4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
    linarith
  unfold lowerScaled
  rw [hlog4y]
  field_simp
  ring
end ThreeSum.PrimeDensity

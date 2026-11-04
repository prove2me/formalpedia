-- Prove2me | solution 1 for ThreeSum.BudgetTime.rational_rpow_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:49:24.904799+00:00
-- url     : https://prove2.me/submissions/5f872130-cd55-4c7a-b25b-c3b809bdb90d

import Definitions.Def_Submission_ThreeSum_UniformStageBounds
import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSum_BudgetTime

set_option autoImplicit false
open ThreeSum ThreeSum.BudgetTime
open Filter Real ThreeSum.Parameters ThreeSum.StageBounds
  ThreeSum.UniformStageBounds
open scoped Topology
set_option maxHeartbeats 400000
namespace ThreeSum.BudgetTime
theorem _root_.solution {r : ℚ} (hr : 0 ≤ r) (n : ℕ) :
    ((n : ℝ) ^ (r : ℝ)) ^ r.den = (n : ℝ) ^ r.num.toNat := by
  have hnum : ((r.num.toNat : ℕ) : ℝ) = (r.num : ℝ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) (Int.toNat_of_nonneg (Rat.num_nonneg.2 hr))
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_nz
  have hmul : (r : ℝ) * (r.den : ℝ) = ((r.num.toNat : ℕ) : ℝ) := by
    rw [Rat.cast_def, hnum]
    field_simp
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n), hmul,
    Real.rpow_natCast]
end ThreeSum.BudgetTime

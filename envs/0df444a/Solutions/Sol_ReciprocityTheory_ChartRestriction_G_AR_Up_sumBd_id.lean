-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:37:23.386868+00:00
-- url     : https://prove2.me/submissions/9bfbf9a7-b131-4116-9e03-619dfc6dde29

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal
noncomputable section
variable {p q : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
theorem _root_.solution (A0 B s : ℝ) (N j : ℕ) (hB : 0 ≤ B) :
    (A0 * ((2 : ℝ) ^ j) ^ 2) ^ N * (B / 4 ^ j) ^ s = A0 ^ N * B ^ s * ((4 : ℝ) ^ N / 4 ^ s) ^ j := by
  have h4 : ((2 : ℝ) ^ j) ^ 2 = (4 : ℝ) ^ j := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have h5 : ((4 : ℝ) ^ j) ^ s = ((4 : ℝ) ^ s) ^ j := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_natCast]
  rw [h4, Real.div_rpow hB (by positivity), mul_pow, div_pow, h5]
  have h6 : (0 : ℝ) < (4 : ℝ) ^ s := by positivity
  field_simp
  ring
end ReciprocityTheory.ChartRestriction.G.AR.Up

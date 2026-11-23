-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.norm_sub_le_max_padic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:15.041982+00:00
-- url     : https://prove2.me/submissions/11e0745e-93ce-43c8-943d-1ea8d4bb254c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsPowerMulUnitNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (x y : ℂ_[l]) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  have h := IsUltrametricDist.dist_triangle_max x 0 y
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, sub_zero, zero_sub, norm_neg] at h
  exact h
end ReciprocityTheory.ChartRestriction.L1

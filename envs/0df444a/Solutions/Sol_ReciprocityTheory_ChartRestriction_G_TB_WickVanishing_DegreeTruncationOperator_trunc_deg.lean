-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator.trunc_deg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:10:45.458361+00:00
-- url     : https://prove2.me/submissions/e3fcbccc-07fc-4560-af57-1fe8fd28de15

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_trunc_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
open SecondColumnDegree
variable {k : Type} [CommRing k] [Algebra ℚ k]
variable {σ : Type} [Fintype σ]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
theorem _root_.solution (N : ℕ) (x : MvPolynomial σ k) : (trunc N x).totalDegree ≤ N := by
  rw [trunc_apply]
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun j hj => ?_)
  by_cases h0 : homogeneousComponent j x = 0
  · rw [h0, totalDegree_zero]
    exact Nat.zero_le _
  · rw [(homogeneousComponent_isHomogeneous j x).totalDegree h0]
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator

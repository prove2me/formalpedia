-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator.trunc_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:10:12.044566+00:00
-- url     : https://prove2.me/submissions/cc39f31d-8a68-4ad1-af18-00a06de844a5

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
theorem _root_.solution (N : ℕ) (x : MvPolynomial σ k) (hx : x.totalDegree ≤ N) : trunc N x = x := by
  rw [trunc_apply]
  conv_rhs => rw [← sum_homogeneousComponent x]
  symm
  refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hx)) ?_
  intro j hj hj'
  apply homogeneousComponent_eq_zero
  simp only [Finset.mem_range] at hj hj'
  omega
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator

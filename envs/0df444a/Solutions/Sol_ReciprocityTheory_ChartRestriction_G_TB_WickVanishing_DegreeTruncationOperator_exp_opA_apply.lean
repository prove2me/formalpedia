-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator.exp_opA_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:54:41.415859+00:00
-- url     : https://prove2.me/submissions/34af9f72-dfc9-4299-99d2-3d66bccde68c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_opA_pow_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_opA_pow_eq_zero

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
theorem _root_.solution (c : σ → σ → k) (t : k) (N : ℕ) (x : MvPolynomial σ k) (hx : x.totalDegree ≤ N) :
    IsNilpotent.exp (opA c t N) x = ∑ i ∈ range (N + 1),
      (algebraMap ℚ k ((i.factorial : ℚ)⁻¹) * t ^ i) • (secondOrder k c)^[i] x := by
  rw [IsNilpotent.exp_eq_sum (opA_pow_eq_zero c t N), LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, opA_pow_apply c t N i x hx, mul_smul, algebraMap_smul]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator

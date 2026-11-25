-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator.opA_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:25:59.824428+00:00
-- url     : https://prove2.me/submissions/92e7b57a-055b-4e9e-97cd-8567712b22ef

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_trunc_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_opA_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_SecondColumnDegree_so_iter_deg_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_SecondColumnDegree_so_smul


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
theorem _root_.solution (c : σ → σ → k) (t : k) (N : ℕ) :
    ∀ (i : ℕ) (x : MvPolynomial σ k), x.totalDegree ≤ N →
      ((opA c t N) ^ i) x = t ^ i • (secondOrder k c)^[i] x
  | 0, x, _ => by simp
  | i + 1, x, hx => by
    rw [pow_succ', Module.End.mul_apply, solution c t N i x hx, opA_apply, trunc_id]
    · rw [so_smul, smul_smul, ← pow_succ', ← Function.iterate_succ_apply' (f := secondOrder k c)]
    · exact (totalDegree_smul_le _ _).trans ((so_iter_deg_le c i x).trans hx)
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator

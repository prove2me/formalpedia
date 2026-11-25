-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator.exp_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:08:14.77756+00:00
-- url     : https://prove2.me/submissions/910b4bd7-d1bd-46cc-b29f-6128d2193379

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_exp_opA_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_prodQ_update
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_prodQ_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_SecondColumnDegree_pderiv_prod_colE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_SecondColumnDegree_so_colB_iter


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
variable {ι : Type} [Fintype ι] {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
theorem _root_.solution (c : ι → ι → k) (t : k) (N : ℕ) (Q : Fin n → MvPolynomial ι k) (b0 : Fin n)
    (hdeg : (prodQ Q).totalDegree ≤ N) :
    IsNilpotent.exp (opA (cB c b0) t N) (prodQ Q) = prodQ (Function.update Q b0 (E1 c t N (Q b0))) := by
  rw [exp_opA_apply _ t N _ hdeg, prodQ_update, prodQ_eq Q b0]
  have hR : ∀ l : ι, pderiv (l, b0) (∏ b ∈ univ.erase b0, colE b (Q b)) = 0 :=
    fun l => pderiv_prod_colE b0 _ (Finset.notMem_erase b0 _) Q l
  unfold E1
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [so_colB_iter c b0 _ hR i, map_smul, smul_mul_assoc]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator.opA_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:37:04.904574+00:00
-- url     : https://prove2.me/submissions/87bd12a1-a944-4ec8-b3eb-69692a4ceb6a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_trunc_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_opA_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_deg_so_trunc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_SecondColumnDegree_so_comm
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
theorem _root_.solution (c1 c2 : σ → σ → k) (t : k) (N : ℕ) : Commute (opA c1 t N) (opA c2 t N) := by
  show opA c1 t N * opA c2 t N = opA c2 t N * opA c1 t N
  refine LinearMap.ext fun x => ?_
  have d1 : (opA c1 t N x).totalDegree ≤ N := by
    rw [opA_apply]
    exact (totalDegree_smul_le _ _).trans (deg_so_trunc c1 N x)
  have d2 : (opA c2 t N x).totalDegree ≤ N := by
    rw [opA_apply]
    exact (totalDegree_smul_le _ _).trans (deg_so_trunc c2 N x)
  rw [Module.End.mul_apply, Module.End.mul_apply, opA_apply c1 t N (opA c2 t N x), trunc_id N _ d2,
    opA_apply c2 t N (opA c1 t N x), trunc_id N _ d1, opA_apply, opA_apply, so_smul, so_smul,
    so_comm]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator

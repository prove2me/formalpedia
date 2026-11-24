-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm_mul_up
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:01.081216+00:00
-- url     : https://prove2.me/submissions/f8efd91e-7ea0-4298-823c-f5c6af9cf606

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_det_lb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_row_expand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_Lm_up
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_Lm_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
open Matrix ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
theorem _root_.solution (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ k : Fin (n + 1), lminor M k ≠ 0)
    (i j : Fin n) (h : j < i) : (Lm M * M) i j = 0 := by
  have hdet : IsUnit (lb M i).det := by rw [det_lb]; exact isUnit_iff_ne_zero.mpr (hM _)
  rw [row_expand (Lm M) M i j (fun k hk => Lm_up M i k hk) (Lm_diag M i)]
  have hL : ∀ k : Fin i, Lm M i (Fin.castLE i.isLt.le k) = -wv M i k := by
    intro k
    simp only [Lm, Matrix.of_apply]
    rw [dif_pos (by simp)]
    rfl
  simp_rw [hL]
  have key : vecMul (wv M i) (lb M i) = fun j : Fin i => M i (Fin.castLE i.isLt.le j) := by
    rw [wv, vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, vecMul_one]
  have hk := congrFun key ⟨j, h⟩
  simp only [vecMul, dotProduct, lb, submatrix_apply] at hk
  have hk' : ∑ k : Fin i, wv M i k * M (Fin.castLE i.isLt.le k) j = M i j := hk
  simp only [neg_mul, Finset.sum_neg_distrib, hk', neg_add_cancel]
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf

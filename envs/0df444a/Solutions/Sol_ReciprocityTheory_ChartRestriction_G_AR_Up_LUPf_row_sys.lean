-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.row_sys
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:31:16.729151+00:00
-- url     : https://prove2.me/submissions/93525bd4-756e-4c5d-9c9b-418073b7205b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_row_expand

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
theorem _root_.solution (N M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (hup : ∀ k : Fin n, i < k → N i k = 0) (hd : N i i = 1)
    (hz : ∀ j : Fin n, j < i → (N * M) i j = 0) :
    vecMul (fun k : Fin i => N i (Fin.castLE i.isLt.le k)) (lb M i) =
      -fun j : Fin i => M i (Fin.castLE i.isLt.le j) := by
  funext j'
  have hrow := row_expand N M i (Fin.castLE i.isLt.le j') hup hd
  rw [hz _ (by simp [Fin.lt_iff_val_lt_val])] at hrow
  simp only [vecMul, dotProduct, lb, submatrix_apply, Pi.neg_apply]
  linear_combination (-1 : ℂ) * hrow
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf

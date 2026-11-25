-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:43:43.318813+00:00
-- url     : https://prove2.me/submissions/1c39629b-687e-4de6-81bb-15d3e509117c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_det_lb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_Lm_up
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_Lm_diag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_row_sys
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_Lm_mul_up

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
theorem _root_.solution (N M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ k : Fin (n + 1), lminor M k ≠ 0)
    (hup : ∀ i k : Fin n, i < k → N i k = 0) (hd : ∀ i, N i i = 1)
    (hz : ∀ i j : Fin n, j < i → (N * M) i j = 0) : N = Lm M := by
  ext i k
  have hdet : IsUnit (lb M i).det := by rw [det_lb]; exact isUnit_iff_ne_zero.mpr (hM _)
  have h1 := row_sys N M i (hup i) (hd i) (hz i)
  have h2 := row_sys (Lm M) M i (fun k hk => Lm_up M i k hk) (Lm_diag M i)
    (fun j hj => Lm_mul_up M hM i j hj)
  have heq : (fun k : Fin i => N i (Fin.castLE i.isLt.le k)) = fun k => Lm M i (Fin.castLE i.isLt.le k) := by
    have h3 := congrArg (fun v => vecMul v (lb M i)⁻¹) (h1.trans h2.symm)
    simpa only [vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, vecMul_one] using h3
  rcases lt_trichotomy k i with hk | rfl | hk
  · exact congrFun heq ⟨k, hk⟩
  · rw [hd, Lm_diag]
  · rw [hup i k hk, Lm_up M i k hk]
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf

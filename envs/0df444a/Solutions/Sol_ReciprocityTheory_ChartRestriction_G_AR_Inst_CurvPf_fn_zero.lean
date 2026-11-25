-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.fn_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:31:38.049089+00:00
-- url     : https://prove2.me/submissions/d92961e3-3942-4375-9c50-a3aa4460cf0d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CoeffMatrixZeroCorrectedLineGramPoly
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DiagonalCurvatureCoefficient
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_Gz_zero

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Polynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P Filter Topology
variable {r m : ℕ} (hm : m ≤ r) (D : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
theorem _root_.solution : fn hm D Y (0 : Fin 1 → ℂ) = ∏ a : Fin m, D (Fin.castLE hm a) := by
  have e : Gnz hm D Y 0 = Dm hm D := by
    unfold Gnz
    rw [Gz_zero]
    simp
  unfold fn
  simp only [Pi.zero_apply]
  rw [e]
  simp [Matrix.det_diagonal, ← Complex.ofReal_prod]
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

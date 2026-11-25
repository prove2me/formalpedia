-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.sum_bas_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:06:51.696999+00:00
-- url     : https://prove2.me/submissions/c536501b-a935-48c3-868a-2b6a717c485d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LogpdAnalytic
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LeviVReLine
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr


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
open ReciprocityTheory.AnForm ReciprocityTheory.L2DbarEstimates Filter Topology
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
theorem _root_.solution {n : ℕ} (ξ : Fin n → ℂ) :
    (∑ k, ((ξ k).re • bas n k + (ξ k).im • (Complex.I • bas n k))) = WithLp.toLp 2 ξ := by
  have h : ∀ k, ((ξ k).re • bas n k + (ξ k).im • (Complex.I • bas n k)) = ξ k • bas n k := fun k => by
    rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul]
    congr 1
    exact Complex.re_add_im (ξ k)
  have hsum : ∑ k, ξ k • bas n k = WithLp.toLp 2 ξ := by
    ext j
    simp [bas, EuclideanSpace.single_apply, Pi.single_apply, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
  simp_rw [h]
  exact hsum
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

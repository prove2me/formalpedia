-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.logpd_analytic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:55:11.909946+00:00
-- url     : https://prove2.me/submissions/35be64e6-dcaa-47d4-93e8-3af7bfd09a31

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DiagonalCurvatureCoefficient
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LogpdAnalytic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_pd_analytic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_pd_zero

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
theorem _root_.solution : AnalyticAt ℂ (fun v => 2 * Complex.log (pd hm Y v)) 0 := by
  have h0 : pd hm Y 0 ∈ Complex.slitPlane := by
    rw [pd_zero]
    exact Complex.one_mem_slitPlane
  exact analyticAt_const.mul ((pd_analytic hm Y).clog h0)
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.levi_logpd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:06:50.453936+00:00
-- url     : https://prove2.me/submissions/14dd95e8-dbce-4794-8fcc-c6df473a5bf5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DiagonalCurvatureCoefficient
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LogpdAnalytic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_logpd_analytic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_logpd_eq
import Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic


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
theorem _root_.solution (w : Fin 1 → ℂ) : levi (fun v => Real.log (‖pd hm Y v‖ ^ 2)) 0 w = 0 := by
  have e : (fun v => Real.log (‖pd hm Y v‖ ^ 2)) = fun v => (2 * Complex.log (pd hm Y v)).re :=
    funext fun v => logpd_eq hm Y v
  rw [e]
  exact levi_re_analytic (logpd_analytic hm Y) w
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

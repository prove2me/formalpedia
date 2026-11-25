-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.leviV_re_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:20:27.966381+00:00
-- url     : https://prove2.me/submissions/79b3116c-9903-47d5-81f3-a713f6bc1cd0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LogpdAnalytic
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LeviVReLine
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_snd_affine
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_lineL_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_sum_bas_re
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_sum_bas_im
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_leviV_re_eq


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
theorem _root_.solution {n : ℕ} (h : V n → ℝ) (z : V n) (hh : ContDiffAt ℝ 2 h z) (ξ : Fin n → ℂ) :
    (leviV n (fun y => (h y : ℂ)) z ξ).re =
      levi (fun v : Fin 1 → ℂ => h (z + lineL (WithLp.toLp 2 ξ) v)) 0 (fun _ => 1) := by
  have e := Y.LocalMaximumSecondDerivative.leviV_re_eq hh ξ
  rw [sum_bas_re, sum_bas_im] at e
  have L0 : z + lineL (WithLp.toLp 2 ξ) 0 = z := by simp [lineL_apply]
  have L1 : lineL (WithLp.toLp 2 ξ) (fun _ => 1) = WithLp.toLp 2 ξ := by simp [lineL_apply]
  have L2 : lineL (WithLp.toLp 2 ξ) (Complex.I • fun _ => 1) = Complex.I • WithLp.toLp 2 ξ := by
    simp [lineL_apply]
  have h0 : ContDiffAt ℝ 2 h (z + lineL (WithLp.toLp 2 ξ) 0) := by rw [L0]; exact hh
  have s1 := snd_affine h z (lineL (WithLp.toLp 2 ξ)) 0 h0 (fun _ => 1)
  have s2 := snd_affine h z (lineL (WithLp.toLp 2 ξ)) 0 h0 (Complex.I • fun _ => 1)
  rw [L0, L1] at s1
  rw [L0, L2] at s2
  unfold levi
  rw [s1, s2]
  linarith
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

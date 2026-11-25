-- Prove2me | solution 1 for ReciprocityTheory.AnForm.Osgood.osgood
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:29:24.490896+00:00
-- url     : https://prove2.me/submissions/e5da7ba5-e8db-45c2-94a0-65eaa17b0d93

import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_OsgoodA
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_kern_analyticAt
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_fctlCLM_kern

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.Osgood
open Complex Metric MeasureTheory Set Filter Topology
open scoped Real
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.Osgood
theorem _root_.solution : OsgoodStatement := by
  intro e U f hU hf x hx
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx)
  have hfd : ∀ ζ ∈ closedBall x r, DifferentiableAt ℂ f ζ := fun ζ hζ =>
    hf.differentiableAt (hU.mem_nhds (hrU hζ))
  have hne : ((2 * π * I) ^ e : ℂ) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)) I_ne_zero)
  have hA : AnalyticAt ℂ
      (fun z => ((2 * π * I) ^ e)⁻¹ * fctlCLM x hr f hfd (kern x r z)) x :=
    analyticAt_const.mul (((fctlCLM x hr f hfd).analyticAt _).comp (kern_analyticAt x hr))
  refine hA.congr ?_
  filter_upwards [ball_mem_nhds x hr] with z hz
  rw [fctlCLM_kern hr hfd hz, inv_mul_cancel_left₀ hne]
end ReciprocityTheory.AnForm.Osgood

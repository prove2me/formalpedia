-- Prove2me | solution 1 for ReciprocityTheory.AnForm.Osgood.fctlCLM_kern
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:21:28.710871+00:00
-- url     : https://prove2.me/submissions/35132383-5916-4580-8609-28d3f2b1ea4c

import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_OsgoodA
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_cubeProj_of_mem
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_kern_apply
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_cauchy_polydisc


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
theorem _root_.solution {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) {f : (Fin n → ℂ) → ℂ}
    (hf : ∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) (hz : z ∈ ball c r) :
    fctlCLM c hr f hf (kern c r z) = (2 * π * I) ^ n * f z := by
  rw [← cauchy_polydisc n f c r hr hf z hz]
  show fctl c r f (kern c r z) = _
  unfold fctl torusIntegral
  refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  dsimp only
  rw [kern_apply hr hz, cubeProj_of_mem hθ, smul_eq_mul, jac]
  ring
end ReciprocityTheory.AnForm.Osgood

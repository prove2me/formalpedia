-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.sh_wd_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:19:34.425237+00:00
-- url     : https://prove2.me/submissions/770cf5fc-12a1-4e2a-a1a3-08e52a1d3347

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ShellA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (n : ℕ) (j : Fin n) (f : V n → ℂ) (y : V n) (hf : DifferentiableAt ℂ f y) :
    wd n j f y = fderiv ℂ f y (bas n j) := by
  have h := (hf.hasFDerivAt.restrictScalars ℝ).fderiv
  rw [wd, h]
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring
end ReciprocityTheory.L2DbarEstimates.I

-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.dualK_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:54:59.669146+00:00
-- url     : https://prove2.me/submissions/3c55db67-429b-4d46-95ed-68a677771098

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_AddLogPosOfThreeQuartersLe
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_add_log_pos_of_three_quarters_le
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_dualK_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
universe u
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {c t : ℝ} (h : 1 ≤ c - t) :
    deriv (dualK c) t = (1 + 1 / (c - t)) / ((c - t) + Real.log (c - t)) := by
  have hev : dualK c =ᶠ[𝓝 t] fun u => -Real.log ((c - u) + Real.log (c - u)) := by
    have : ∀ᶠ u in 𝓝 t, u < t + 1 / 8 := eventually_lt_nhds (by linarith)
    filter_upwards [this] with u hu
    exact dualK_eq (by linarith)
  rw [hev.deriv_eq]
  have hs0 : c - t ≠ 0 := by linarith
  have hpos : 0 < (c - t) + Real.log (c - t) := add_log_pos_of_three_quarters_le (by linarith)
  have h1 : HasDerivAt (fun u : ℝ => c - u) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub c
  have h2 := h1.log hs0
  have h4 : HasDerivAt (fun u => -Real.log ((c - u) + Real.log (c - u)))
      (-((-1 + -1 / (c - t)) / ((c - t) + Real.log (c - t)))) t :=
    ((h1.add h2).log hpos.ne').neg
  rw [h4.deriv]
  field_simp
  ring
end ReciprocityTheory.L2DbarEstimates.I

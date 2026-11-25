-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.dualK_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:05:57.726598+00:00
-- url     : https://prove2.me/submissions/1b4f5e48-980f-4efc-959e-4f99e70ca5b2

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_AddLogPosOfThreeQuartersLe
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_dualSig_contDiff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_dualSig_ge
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_add_log_pos_of_three_quarters_le
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub


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
theorem _root_.solution (c : ℝ) : ContDiff ℝ ∞ (dualK c) := by
  have hs : ContDiff ℝ ∞ (fun t : ℝ => dualSig (c - t)) :=
    dualSig_contDiff.comp (contDiff_const.sub contDiff_id)
  have hpos : ∀ t, 0 < dualSig (c - t) := fun t => by linarith [dualSig_ge (c - t)]
  have hl : ContDiff ℝ ∞ (fun t : ℝ => Real.log (dualSig (c - t))) :=
    hs.log (fun t => (hpos t).ne')
  have hsum : ContDiff ℝ ∞ (fun t : ℝ => dualSig (c - t) + Real.log (dualSig (c - t))) := hs.add hl
  have := hsum.log (fun t => (add_log_pos_of_three_quarters_le (dualSig_ge (c - t))).ne')
  exact this.neg
end ReciprocityTheory.L2DbarEstimates.I

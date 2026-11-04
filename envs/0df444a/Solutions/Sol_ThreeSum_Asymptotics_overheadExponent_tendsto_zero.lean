-- Prove2me | solution 1 for ThreeSum.Asymptotics.overheadExponent_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:14:27.954932+00:00
-- url     : https://prove2.me/submissions/bd1357d6-f330-4f71-9a74-b8633f06b19a

import Definitions.Def_Submission_ThreeSum_Parameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Theorems.Thm_ThreeSum_Asymptotics_log_nat_tendsto_atTop

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Asymptotics
open Filter Real _root_.Asymptotics
open ThreeSum.Parameters
open scoped Topology
set_option maxRecDepth 10000
namespace ThreeSum.Asymptotics
theorem _root_.solution (C : ℝ) :
    Tendsto (overheadExponent C) atTop (𝓝 0) := by
  unfold overheadExponent
  have hthird := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
    log_nat_tendsto_atTop
  have hhalf := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
    log_nat_tendsto_atTop
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).tendsto_div_nhds_zero.comp
    log_nat_tendsto_atTop
  have hinv := log_nat_tendsto_atTop.inv_tendsto_atTop
  simpa [Function.comp_def] using
    (hthird.add hhalf |>.add hlog |>.add hinv).const_mul C
end ThreeSum.Asymptotics

-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.continuous_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:20:51.183+00:00
-- url     : https://prove2.me/submissions/1f23d32c-6e21-4df0-87b7-5b5f4e2f3db3

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_SliceArch
import Theorems.Thm_PositivityTheory_ThKCT_Arch_S_add
import Theorems.Thm_PositivityTheory_ThKCT_Arch_tendsto_S

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKCT PositivityTheory.ThKCT.Arch
open scoped ContDiff NNReal
open Complex Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace PositivityTheory.ThKCT.Arch
theorem _root_.solution (f : SchwartzMap V ℂ) : Continuous fun w => S w f := by
  refine continuous_iff_continuousAt.2 fun w => ?_
  have h1 : Tendsto (fun u => u - w) (𝓝 w) (𝓝 0) := by simpa using (continuous_sub_right w).tendsto w
  have h2 : Continuous fun h : V × (V →L[ℝ] ℝ) => cexp (I * ((w.2 h.1 - h.2 w.1) / 2 : ℝ)) := by fun_prop
  have h3 := ((h2.tendsto 0).smul (((S w).continuous.tendsto f).comp (tendsto_S f))).comp h1
  simp only [Prod.fst_zero, Prod.snd_zero, map_zero, ContinuousLinearMap.zero_apply, sub_self, zero_div, ofReal_zero, mul_zero,
    Complex.exp_zero, one_smul] at h3
  refine h3.congr fun u => ?_
  simp only [Function.comp_apply]
  rw [← S_add, add_sub_cancel]
end PositivityTheory.ThKCT.Arch
